#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cctype>
#include <cmath>
#include <condition_variable>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <deque>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <numeric>
#include <optional>
#include <queue>
#include <random>
#include <regex>
#include <set>
#include <shared_mutex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <thread>
#include <tuple>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <sqlite3.h>
#include <curl/curl.h>

#include <sys/stat.h>
#include <unistd.h>

namespace fs = std::filesystem;

namespace infinity {

constexpr std::size_t HDV_DIM = 8192;
constexpr std::size_t MAX_TRIPLES = 500000;
constexpr std::size_t FTS_LIMIT = 20;
constexpr int DEFAULT_CRAWLER_THREADS = 30;
constexpr int SLOW_CRAWLER_THREADS = 5;
constexpr std::chrono::seconds CONSCIOUSNESS_TICK(5);
constexpr double EPSILON_GREEDY = 0.10;
constexpr double ENTROPY_THRESHOLD = 1.35;
constexpr float WEIGHT_FLOOR = 0.01f;
constexpr float WEIGHT_CEILING = 25.0f;
constexpr float CERTAINTY_FLOOR = 0.01f;
constexpr float CERTAINTY_CEILING = 1.0f;

constexpr const char* COLOR_RESET = "\033[0m";
constexpr const char* COLOR_RED = "\033[31m";
constexpr const char* COLOR_GREEN = "\033[32m";
constexpr const char* COLOR_YELLOW = "\033[33m";
constexpr const char* COLOR_BLUE = "\033[34m";
constexpr const char* COLOR_MAGENTA = "\033[35m";
constexpr const char* COLOR_CYAN = "\033[36m";
constexpr const char* COLOR_WHITE = "\033[1;37m";

std::atomic<bool> g_shutdown_requested{false};

std::string lower_copy(std::string value) {
    std::transform(value.begin(), value.end(), value.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return value;
}

std::string upper_copy(std::string value) {
    std::transform(value.begin(), value.end(), value.begin(),
                   [](unsigned char c) { return static_cast<char>(std::toupper(c)); });
    return value;
}

std::string trim_copy(std::string value) {
    auto not_space = [](unsigned char c) { return !std::isspace(c); };
    auto begin = std::find_if(value.begin(), value.end(), not_space);
    auto end = std::find_if(value.rbegin(), value.rend(), not_space).base();
    if (begin >= end) {
        return {};
    }
    return std::string(begin, end);
}

std::vector<std::string> split_words(const std::string& text) {
    std::vector<std::string> out;
    std::string current;
    for (char raw : text) {
        unsigned char c = static_cast<unsigned char>(raw);
        if (std::isalnum(c) || raw == '_' || raw == '-') {
            current.push_back(static_cast<char>(std::tolower(c)));
        } else if (!current.empty()) {
            out.push_back(current);
            current.clear();
        }
    }
    if (!current.empty()) {
        out.push_back(current);
    }
    return out;
}

std::vector<std::string> split_sentences(const std::string& text) {
    std::vector<std::string> out;
    std::string current;
    for (char c : text) {
        current.push_back(c);
        if ((c == '.' || c == '!' || c == '?') && current.size() >= 24) {
            out.push_back(trim_copy(current));
            current.clear();
        }
    }
    if (!trim_copy(current).empty()) {
        out.push_back(trim_copy(current));
    }
    return out;
}

std::string join_strings(const std::vector<std::string>& values, const std::string& delim) {
    std::ostringstream oss;
    for (std::size_t i = 0; i < values.size(); ++i) {
        if (i != 0) {
            oss << delim;
        }
        oss << values[i];
    }
    return oss.str();
}

std::string now_string() {
    const std::time_t now = std::time(nullptr);
    std::tm tm_buf{};
    localtime_r(&now, &tm_buf);
    char buffer[32];
    std::strftime(buffer, sizeof(buffer), "%Y-%m-%d %H:%M:%S", &tm_buf);
    return buffer;
}

int64_t now_epoch() {
    return static_cast<int64_t>(std::time(nullptr));
}

std::string format_double(double value, int precision = 3) {
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(precision) << value;
    return oss.str();
}

double clamp_double(double value, double lo, double hi) {
    return std::max(lo, std::min(hi, value));
}

template <typename T>
T clamp_value(T value, T lo, T hi) {
    return std::max(lo, std::min(hi, value));
}

class Logger {
public:
    static void console(const std::string& tag, const std::string& message,
                        const char* color = COLOR_WHITE) {
        std::lock_guard<std::mutex> lock(console_mutex());
        std::cout << color << "[" << now_string() << "][" << tag << "] "
                  << COLOR_RESET << message << "\n" << std::flush;
    }

    static bool append_file(const std::string& path, const std::string& line) {
        std::lock_guard<std::mutex> lock(file_mutex(path));
        std::ofstream out(path, std::ios::app);
        if (!out) {
            console("IO", "Failed to write " + path, COLOR_RED);
            return false;
        }
        out << line << "\n";
        if (!out.good()) {
            console("IO", "Disk write failure for " + path, COLOR_RED);
            return false;
        }
        return true;
    }

private:
    static std::mutex& console_mutex() {
        static std::mutex mutex;
        return mutex;
    }

    static std::mutex& registry_mutex() {
        static std::mutex mutex;
        return mutex;
    }

    static std::mutex& file_mutex(const std::string& path) {
        static std::unordered_map<std::string, std::unique_ptr<std::mutex>> registry;
        std::lock_guard<std::mutex> lock(registry_mutex());
        auto& entry = registry[path];
        if (!entry) {
            entry = std::make_unique<std::mutex>();
        }
        return *entry;
    }
};

namespace crypto {

struct Digest256 {
    std::array<uint32_t, 8> words{};
};

namespace detail {

constexpr std::array<uint32_t, 64> K = {
    0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
    0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
    0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
    0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
    0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
    0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
    0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
    0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
    0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
    0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
    0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
    0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
    0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
    0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
    0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
    0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
};

inline uint32_t rotr(uint32_t value, unsigned shift) {
    return (value >> shift) | (value << (32u - shift));
}

}  // namespace detail

Digest256 sha256(std::vector<uint8_t> message) {
    uint32_t h0 = 0x6a09e667u;
    uint32_t h1 = 0xbb67ae85u;
    uint32_t h2 = 0x3c6ef372u;
    uint32_t h3 = 0xa54ff53au;
    uint32_t h4 = 0x510e527fu;
    uint32_t h5 = 0x9b05688cu;
    uint32_t h6 = 0x1f83d9abu;
    uint32_t h7 = 0x5be0cd19u;

    const uint64_t bit_length = static_cast<uint64_t>(message.size()) * 8ULL;
    message.push_back(0x80u);
    while ((message.size() % 64U) != 56U) {
        message.push_back(0);
    }
    for (int i = 7; i >= 0; --i) {
        message.push_back(static_cast<uint8_t>((bit_length >> (i * 8)) & 0xFFu));
    }

    for (std::size_t block = 0; block < message.size(); block += 64U) {
        std::array<uint32_t, 64> schedule{};
        for (int j = 0; j < 16; ++j) {
            schedule[j] =
                (static_cast<uint32_t>(message[block + j * 4]) << 24) |
                (static_cast<uint32_t>(message[block + j * 4 + 1]) << 16) |
                (static_cast<uint32_t>(message[block + j * 4 + 2]) << 8) |
                static_cast<uint32_t>(message[block + j * 4 + 3]);
        }
        for (int j = 16; j < 64; ++j) {
            const uint32_t s0 = detail::rotr(schedule[j - 15], 7) ^
                                detail::rotr(schedule[j - 15], 18) ^
                                (schedule[j - 15] >> 3);
            const uint32_t s1 = detail::rotr(schedule[j - 2], 17) ^
                                detail::rotr(schedule[j - 2], 19) ^
                                (schedule[j - 2] >> 10);
            schedule[j] = schedule[j - 16] + s0 + schedule[j - 7] + s1;
        }

        uint32_t a = h0;
        uint32_t b = h1;
        uint32_t c = h2;
        uint32_t d = h3;
        uint32_t e = h4;
        uint32_t f = h5;
        uint32_t g = h6;
        uint32_t h = h7;

        for (int j = 0; j < 64; ++j) {
            const uint32_t s1 = detail::rotr(e, 6) ^ detail::rotr(e, 11) ^ detail::rotr(e, 25);
            const uint32_t choose = (e & f) ^ (~e & g);
            const uint32_t temp1 = h + s1 + choose + detail::K[j] + schedule[j];
            const uint32_t s0 = detail::rotr(a, 2) ^ detail::rotr(a, 13) ^ detail::rotr(a, 22);
            const uint32_t majority = (a & b) ^ (a & c) ^ (b & c);
            const uint32_t temp2 = s0 + majority;

            h = g;
            g = f;
            f = e;
            e = d + temp1;
            d = c;
            c = b;
            b = a;
            a = temp1 + temp2;
        }

        h0 += a;
        h1 += b;
        h2 += c;
        h3 += d;
        h4 += e;
        h5 += f;
        h6 += g;
        h7 += h;
    }

    return {{{h0, h1, h2, h3, h4, h5, h6, h7}}};
}

Digest256 hmac_sha256(const std::array<uint8_t, 32>& key, const std::vector<uint8_t>& message) {
    std::array<uint8_t, 64> key_pad{};
    std::copy(key.begin(), key.end(), key_pad.begin());

    std::array<uint8_t, 64> inner_pad{};
    std::array<uint8_t, 64> outer_pad{};
    for (int i = 0; i < 64; ++i) {
        inner_pad[i] = static_cast<uint8_t>(key_pad[i] ^ 0x36u);
        outer_pad[i] = static_cast<uint8_t>(key_pad[i] ^ 0x5cu);
    }

    std::vector<uint8_t> inner(inner_pad.begin(), inner_pad.end());
    inner.insert(inner.end(), message.begin(), message.end());
    const Digest256 inner_digest = sha256(inner);

    std::vector<uint8_t> outer(outer_pad.begin(), outer_pad.end());
    for (int i = 0; i < 8; ++i) {
        for (int j = 0; j < 4; ++j) {
            outer.push_back(static_cast<uint8_t>((inner_digest.words[i] >> (24 - j * 8)) & 0xFFu));
        }
    }
    return sha256(outer);
}

std::string to_hex(const Digest256& digest) {
    std::ostringstream oss;
    oss << std::hex << std::setfill('0');
    for (uint32_t word : digest.words) {
        oss << std::setw(8) << word;
    }
    return oss.str();
}

}  // namespace crypto

class ROSHANReceptor {
public:
    explicit ROSHANReceptor(std::string_view passphrase) {
        derive_key(passphrase);
    }

    std::string sign(std::string_view message) const {
        std::vector<uint8_t> bytes(message.begin(), message.end());
        return crypto::to_hex(crypto::hmac_sha256(key_, bytes));
    }

    bool verify(std::string_view message, std::string_view token) {
        if (defense_mode_.load()) {
            return false;
        }
        const bool valid = sign(message) == token;
        if (!valid) {
            const uint32_t failures = failed_attempts_.fetch_add(1) + 1;
            if (failures >= 3U) {
                defense_mode_.store(true);
            }
        } else {
            failed_attempts_.store(0);
        }
        return valid;
    }

    void reset_defense(std::string_view passphrase) {
        ROSHANReceptor probe(passphrase);
        if (probe.key_ == key_) {
            failed_attempts_.store(0);
            defense_mode_.store(false);
        }
    }

    bool defense_mode() const noexcept {
        return defense_mode_.load();
    }

private:
    void derive_key(std::string_view passphrase) {
        std::vector<uint8_t> payload(passphrase.begin(), passphrase.end());
        const crypto::Digest256 digest = crypto::sha256(payload);
        for (int i = 0; i < 8; ++i) {
            for (int j = 0; j < 4; ++j) {
                key_[static_cast<std::size_t>(i) * 4U + static_cast<std::size_t>(j)] =
                    static_cast<uint8_t>((digest.words[i] >> (24 - j * 8)) & 0xFFu);
            }
        }
    }

    std::array<uint8_t, 32> key_{};
    std::atomic<uint32_t> failed_attempts_{0};
    std::atomic<bool> defense_mode_{false};
};

struct HttpResponse {
    bool ok{false};
    long code{0};
    std::string body;
    std::string error;
};

class HttpClient {
public:
    static HttpResponse get(const std::string& url, long timeout_seconds = 15, bool head_only = false) {
        HttpResponse last;
        for (int attempt = 0; attempt < 3; ++attempt) {
            CURL* curl = curl_easy_init();
            if (!curl) {
                last.error = "curl_easy_init failed";
                break;
            }

            std::string body;
            auto setopt = [&](CURLoption option, auto value) {
                const CURLcode option_rc = curl_easy_setopt(curl, option, value);
                if (option_rc != CURLE_OK) {
                    last.ok = false;
                    last.error = curl_easy_strerror(option_rc);
                    return false;
                }
                return true;
            };

            if (!setopt(CURLOPT_URL, url.c_str()) ||
                !setopt(CURLOPT_WRITEFUNCTION, &HttpClient::write_callback) ||
                !setopt(CURLOPT_WRITEDATA, &body) ||
                !setopt(CURLOPT_USERAGENT, "INFINITY-Organism/4.0") ||
                !setopt(CURLOPT_TIMEOUT, timeout_seconds) ||
                !setopt(CURLOPT_FOLLOWLOCATION, 1L) ||
                !setopt(CURLOPT_SSL_VERIFYPEER, 1L) ||
                !setopt(CURLOPT_SSL_VERIFYHOST, 2L) ||
                !setopt(CURLOPT_ACCEPT_ENCODING, "")) {
                curl_easy_cleanup(curl);
                std::this_thread::sleep_for(std::chrono::milliseconds(200 * (attempt + 1)));
                continue;
            }
            if (head_only && !setopt(CURLOPT_NOBODY, 1L)) {
                curl_easy_cleanup(curl);
                std::this_thread::sleep_for(std::chrono::milliseconds(200 * (attempt + 1)));
                continue;
            }

            const CURLcode rc = curl_easy_perform(curl);
            const CURLcode info_rc = curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &last.code);
            if (rc == CURLE_OK && info_rc == CURLE_OK && last.code >= 200 && last.code < 400) {
                last.ok = true;
                last.body = std::move(body);
                curl_easy_cleanup(curl);
                return last;
            }

            last.ok = false;
            last.body = std::move(body);
            last.error = rc != CURLE_OK ? curl_easy_strerror(rc) : curl_easy_strerror(info_rc);
            curl_easy_cleanup(curl);
            std::this_thread::sleep_for(std::chrono::milliseconds(200 * (attempt + 1)));
        }
        return last;
    }

private:
    static std::size_t write_callback(char* ptr, std::size_t size, std::size_t nmemb, void* userdata) {
        std::string* target = static_cast<std::string*>(userdata);
        target->append(ptr, size * nmemb);
        return size * nmemb;
    }
};

using HDV = std::array<float, HDV_DIM>;

namespace hdv {

HDV random_atom(uint64_t seed) {
    std::mt19937_64 rng(seed);
    std::normal_distribution<float> dist(0.0f, 1.0f / std::sqrt(static_cast<float>(HDV_DIM)));
    HDV vec{};
    for (float& value : vec) {
        value = dist(rng);
    }
    return vec;
}

HDV normalise(HDV vec) {
    float sum = 0.0f;
    for (float value : vec) {
        sum += value * value;
    }
    const float norm = std::sqrt(sum);
    if (norm > 1e-9f) {
        for (float& value : vec) {
            value /= norm;
        }
    }
    return vec;
}

HDV encode(std::string_view label) {
    uint64_t hash = 14695981039346656037ull;
    for (unsigned char c : label) {
        hash = (hash ^ c) * 1099511628211ull;
    }
    return normalise(random_atom(hash));
}

float similarity(const HDV& a, const HDV& b) {
    float dot = 0.0f;
    for (std::size_t i = 0; i < HDV_DIM; ++i) {
        dot += a[i] * b[i];
    }
    return dot;
}

HDV bundle(const HDV& a, const HDV& b, float wa = 1.0f, float wb = 1.0f) {
    HDV out{};
    for (std::size_t i = 0; i < HDV_DIM; ++i) {
        out[i] = wa * a[i] + wb * b[i];
    }
    return normalise(out);
}

HDV bind(const HDV& a, const HDV& b) {
    HDV out{};
    for (std::size_t i = 0; i < HDV_DIM; ++i) {
        out[i] = a[i] * b[i];
    }
    return normalise(out);
}

HDV triple(const HDV& subject, const HDV& relation, const HDV& object) {
    return hdv::bind(subject, hdv::bind(relation, object));
}

}  // namespace hdv

class HDVPool {
public:
    std::shared_ptr<const HDV> allocate(HDV vec) {
        std::lock_guard<std::mutex> lock(mutex_);
        storage_.push_back(std::move(vec));
        const HDV* ptr = &storage_.back();
        return std::shared_ptr<const HDV>(ptr, [](const HDV*) {});
    }

private:
    std::mutex mutex_;
    std::deque<HDV> storage_;
};

class LSHIndex {
public:
    LSHIndex() {
        for (uint64_t seed = 1; seed <= 16; ++seed) {
            hyperplanes_.push_back(hdv::encode("LSH_" + std::to_string(seed)));
        }
    }

    uint32_t signature(const HDV& vec) const {
        uint32_t sig = 0;
        for (std::size_t i = 0; i < hyperplanes_.size(); ++i) {
            if (hdv::similarity(vec, hyperplanes_[i]) >= 0.0f) {
                sig |= (1u << i);
            }
        }
        return sig;
    }

    void insert(const std::string& label, const HDV& vec) {
        buckets_[signature(vec)].push_back(label);
    }

    std::vector<std::string> candidates(const HDV& vec) const {
        std::vector<std::string> out;
        const uint32_t sig = signature(vec);
        auto append_bucket = [&](uint32_t key) {
            auto it = buckets_.find(key);
            if (it != buckets_.end()) {
                out.insert(out.end(), it->second.begin(), it->second.end());
            }
        };
        append_bucket(sig);
        for (int bit = 0; bit < 16; ++bit) {
            append_bucket(sig ^ (1u << bit));
        }
        return out;
    }

private:
    std::vector<HDV> hyperplanes_;
    std::unordered_map<uint32_t, std::vector<std::string>> buckets_;
};

class SymbolEncoder {
public:
    std::shared_ptr<const HDV> encode(const std::string& label) {
        {
            std::shared_lock<std::shared_mutex> lock(mutex_);
            auto it = cache_.find(label);
            if (it != cache_.end()) {
                return it->second;
            }
        }

        std::shared_ptr<const HDV> ptr = pool_.allocate(hdv::encode(label));
        std::unique_lock<std::shared_mutex> lock(mutex_);
        auto [it, inserted] = cache_.emplace(label, ptr);
        if (inserted) {
            lsh_.insert(label, *ptr);
        }
        return it->second;
    }

    std::vector<std::pair<std::string, float>> nearest(const std::string& term, std::size_t limit) const {
        std::shared_ptr<const HDV> query;
        {
            std::shared_lock<std::shared_mutex> lock(mutex_);
            auto it = cache_.find(term);
            if (it != cache_.end()) {
                query = it->second;
            }
        }
        if (!query) {
            query = pool_.allocate(hdv::encode(term));
        }

        std::vector<std::string> labels;
        {
            std::shared_lock<std::shared_mutex> lock(mutex_);
            if (cache_.size() > 10000U) {
                labels = lsh_.candidates(*query);
            } else {
                labels.reserve(cache_.size());
                for (const auto& entry : cache_) {
                    labels.push_back(entry.first);
                }
            }
        }

        std::vector<std::pair<std::string, float>> scored;
        scored.reserve(labels.size());
        {
            std::shared_lock<std::shared_mutex> lock(mutex_);
            for (const std::string& label : labels) {
                auto it = cache_.find(label);
                if (it == cache_.end()) {
                    continue;
                }
                scored.emplace_back(label, hdv::similarity(*query, *it->second));
            }
        }
        const std::size_t k = std::min(limit, scored.size());
        std::partial_sort(scored.begin(), scored.begin() + k, scored.end(),
                          [](const auto& a, const auto& b) { return a.second > b.second; });
        scored.resize(k);
        return scored;
    }

private:
    mutable HDVPool pool_;
    mutable std::shared_mutex mutex_;
    mutable LSHIndex lsh_;
    std::unordered_map<std::string, std::shared_ptr<const HDV>> cache_;
};

enum class TemporalState {
    Past,
    Present,
    Future,
    Unknown
};

std::string temporal_name(TemporalState state) {
    switch (state) {
        case TemporalState::Past:
            return "PAST";
        case TemporalState::Present:
            return "PRESENT";
        case TemporalState::Future:
            return "FUTURE";
        case TemporalState::Unknown:
        default:
            return "UNKNOWN";
    }
}

struct TripleRecord {
    int64_t id{0};
    std::string subject;
    std::string relation;
    std::string object;
    float weight{1.0f};
    float certainty{0.55f};
    int64_t first_seen{0};
    int64_t last_seen{0};
    int64_t last_access{0};
    uint64_t access_count{0};
    bool contradiction_flag{false};
    bool quarantined{false};
    TemporalState temporal{TemporalState::Present};
    std::set<std::string> sources;
};

struct UpsertResult {
    int64_t id{-1};
    bool inserted{false};
    std::size_t pruned{0};
};

std::string triple_key(const std::string& subject, const std::string& relation, const std::string& object) {
    return subject + "\x1f" + relation + "\x1f" + object;
}

class KnowledgeMesh {
public:
    explicit KnowledgeMesh(SymbolEncoder& encoder)
        : encoder_(encoder) {}

    UpsertResult upsert(const std::string& subject,
                        const std::string& relation,
                        const std::string& object,
                        const std::string& source,
                        float certainty,
                        TemporalState temporal = TemporalState::Present) {
        const std::string key = triple_key(subject, relation, object);
        const int64_t now = now_epoch();

        std::unique_lock<std::shared_mutex> lock(mutex_);
        ensure_concept_unlocked(subject);
        ensure_concept_unlocked(relation);
        ensure_concept_unlocked(object);

        auto it = key_to_id_.find(key);
        if (it != key_to_id_.end()) {
            TripleRecord& record = triples_.at(it->second);
            record.weight = clamp_value(record.weight + 0.12f, WEIGHT_FLOOR, WEIGHT_CEILING);
            record.certainty = clamp_value((record.certainty + certainty) * 0.5f, CERTAINTY_FLOOR, CERTAINTY_CEILING);
            record.last_seen = now;
            record.temporal = temporal;
            if (!source.empty()) {
                record.sources.insert(source);
            }
            return {record.id, false, 0};
        }

        std::size_t pruned = 0;
        if (triples_.size() >= MAX_TRIPLES) {
            pruned = prune_lowest_weight_unlocked(256);
            if (triples_.size() >= MAX_TRIPLES) {
                return {-1, false, pruned};
            }
        }

        TripleRecord record;
        record.id = next_id_++;
        record.subject = subject;
        record.relation = relation;
        record.object = object;
        record.weight = 1.0f;
        record.certainty = clamp_value(certainty, CERTAINTY_FLOOR, CERTAINTY_CEILING);
        record.first_seen = now;
        record.last_seen = now;
        record.last_access = now;
        record.temporal = temporal;
        if (!source.empty()) {
            record.sources.insert(source);
        }

        key_to_id_[key] = record.id;
        triples_.emplace(record.id, record);
        subject_index_[subject].push_back(record.id);
        object_index_[object].push_back(record.id);
        relation_index_[relation].push_back(record.id);
        degree_[subject] += 1;
        degree_[object] += 1;
        hebbian_reinforce_unlocked(subject, object);
        return {record.id, true, pruned};
    }

    bool contains_exact(const std::string& subject, const std::string& relation, const std::string& object) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        return key_to_id_.count(triple_key(subject, relation, object)) != 0U;
    }

    std::optional<TripleRecord> get_exact(const std::string& subject, const std::string& relation, const std::string& object) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        auto it = key_to_id_.find(triple_key(subject, relation, object));
        if (it == key_to_id_.end()) {
            return std::nullopt;
        }
        return triples_.at(it->second);
    }

    std::optional<TripleRecord> get_by_id(int64_t id) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        auto it = triples_.find(id);
        if (it == triples_.end()) {
            return std::nullopt;
        }
        return it->second;
    }

    std::vector<TripleRecord> snapshot() const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        std::vector<TripleRecord> out;
        out.reserve(triples_.size());
        for (const auto& entry : triples_) {
            out.push_back(entry.second);
        }
        return out;
    }

    std::vector<TripleRecord> triples_for_concept(const std::string& cname, std::size_t limit = 20) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        std::vector<TripleRecord> out;
        auto collect = [&](const auto& index) {
            auto it = index.find(cname);
            if (it == index.end()) {
                return;
            }
            for (int64_t id : it->second) {
                auto found = triples_.find(id);
                if (found != triples_.end()) {
                    out.push_back(found->second);
                    if (out.size() >= limit) {
                        return;
                    }
                }
            }
        };
        collect(subject_index_);
        if (out.size() < limit) {
            collect(object_index_);
        }
        return out;
    }

    std::vector<TripleRecord> outgoing(const std::string& subject) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        std::vector<TripleRecord> out;
        auto it = subject_index_.find(subject);
        if (it == subject_index_.end()) {
            return out;
        }
        out.reserve(it->second.size());
        for (int64_t id : it->second) {
            auto found = triples_.find(id);
            if (found != triples_.end()) {
                out.push_back(found->second);
            }
        }
        return out;
    }

    std::set<std::string> all_concepts() const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        std::set<std::string> out;
        for (const auto& entry : concept_vectors_) {
            out.insert(entry.first);
        }
        return out;
    }

    float concept_similarity(const std::string& left, const std::string& right) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        auto left_it = concept_vectors_.find(left);
        auto right_it = concept_vectors_.find(right);
        if (left_it == concept_vectors_.end() || right_it == concept_vectors_.end()) {
            return 0.0f;
        }
        const float base = hdv::similarity(*left_it->second, *right_it->second);
        const auto affinity_it = pair_affinity_.find(left + "\x1f" + right);
        const float affinity = affinity_it == pair_affinity_.end() ? 0.0f : affinity_it->second;
        return clamp_value(base + affinity * 0.05f, -1.0f, 1.0f);
    }

    std::string dominant_relation(const std::string& cname) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        std::unordered_map<std::string, double> scores;
        auto it = subject_index_.find(cname);
        if (it != subject_index_.end()) {
            for (int64_t id : it->second) {
                auto triple_it = triples_.find(id);
                if (triple_it != triples_.end()) {
                    scores[triple_it->second.relation] += triple_it->second.weight * triple_it->second.certainty;
                }
            }
        }
        std::string best = "RELATES_TO";
        double score = 0.0;
        for (const auto& entry : scores) {
            if (entry.second > score) {
                score = entry.second;
                best = entry.first;
            }
        }
        return best;
    }

    void mark_accessed(int64_t id) {
        std::unique_lock<std::shared_mutex> lock(mutex_);
        auto it = triples_.find(id);
        if (it == triples_.end()) {
            return;
        }
        it->second.access_count += 1;
        it->second.last_access = now_epoch();
        it->second.weight = clamp_value(it->second.weight + 0.02f, WEIGHT_FLOOR, WEIGHT_CEILING);
    }

    void adjust_weight(int64_t id, float delta) {
        std::unique_lock<std::shared_mutex> lock(mutex_);
        auto it = triples_.find(id);
        if (it == triples_.end()) {
            return;
        }
        it->second.weight = clamp_value(it->second.weight + delta, WEIGHT_FLOOR, WEIGHT_CEILING);
    }

    void scale_certainty(int64_t id, float factor) {
        std::unique_lock<std::shared_mutex> lock(mutex_);
        auto it = triples_.find(id);
        if (it == triples_.end()) {
            return;
        }
        it->second.certainty = clamp_value(it->second.certainty * factor, CERTAINTY_FLOOR, CERTAINTY_CEILING);
    }

    void flag_contradiction(int64_t id, bool value) {
        std::unique_lock<std::shared_mutex> lock(mutex_);
        auto it = triples_.find(id);
        if (it == triples_.end()) {
            return;
        }
        it->second.contradiction_flag = value;
    }

    void set_quarantined(int64_t id, bool value) {
        std::unique_lock<std::shared_mutex> lock(mutex_);
        auto it = triples_.find(id);
        if (it == triples_.end()) {
            return;
        }
        it->second.quarantined = value;
    }

    std::size_t corroboration_count(int64_t id) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        auto it = triples_.find(id);
        if (it == triples_.end()) {
            return 0;
        }
        return it->second.sources.size();
    }

    std::size_t size() const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        return triples_.size();
    }

    std::size_t concept_count() const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        return concept_vectors_.size();
    }

    std::size_t sparse_node_count() const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        std::size_t sparse = 0;
        for (const auto& entry : concept_vectors_) {
            auto degree_it = degree_.find(entry.first);
            const int degree = degree_it == degree_.end() ? 0 : degree_it->second;
            if (degree < 3) {
                sparse += 1;
            }
        }
        return sparse;
    }

    double sparse_ratio() const {
        const std::size_t count = concept_count();
        if (count == 0U) {
            return 1.0;
        }
        return static_cast<double>(sparse_node_count()) / static_cast<double>(count);
    }

    float local_entropy(const std::string& cname) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        return local_entropy_unlocked(cname);
    }

    double global_entropy() const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        if (concept_vectors_.empty()) {
            return 0.0;
        }
        double total = 0.0;
        for (const auto& entry : concept_vectors_) {
            total += local_entropy_unlocked(entry.first);
        }
        return total / static_cast<double>(concept_vectors_.size());
    }

    std::vector<std::pair<std::string, float>> entropy_ranking(std::size_t limit) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        std::vector<std::pair<std::string, float>> scored;
        scored.reserve(concept_vectors_.size());
        for (const auto& entry : concept_vectors_) {
            scored.emplace_back(entry.first, local_entropy_unlocked(entry.first));
        }
        const std::size_t k = std::min(limit, scored.size());
        std::partial_sort(scored.begin(), scored.begin() + k, scored.end(),
                          [](const auto& a, const auto& b) { return a.second > b.second; });
        scored.resize(k);
        return scored;
    }

    std::vector<std::pair<std::string, float>> nearest_concepts(const std::string& term, std::size_t limit) const {
        return encoder_.nearest(term, limit);
    }

    std::vector<std::pair<TripleRecord, float>> semantic_recall(const std::string& query, std::size_t limit) const {
        std::shared_lock<std::shared_mutex> lock(mutex_);
        const auto query_vec = encoder_.encode(query);
        std::vector<std::pair<TripleRecord, float>> scored;
        scored.reserve(triples_.size());
        const bool approximate = concept_vectors_.size() > 10000U;
        std::unordered_set<std::string> concept_filter;
        if (approximate) {
            for (const auto& item : encoder_.nearest(query, 64)) {
                concept_filter.insert(item.first);
            }
        }
        for (const auto& entry : triples_) {
            const TripleRecord& triple = entry.second;
            if (approximate &&
                concept_filter.count(triple.subject) == 0U &&
                concept_filter.count(triple.object) == 0U &&
                concept_filter.count(triple.relation) == 0U) {
                continue;
            }
            const auto subject_vec = concept_vectors_.at(triple.subject);
            const auto relation_vec = concept_vectors_.at(triple.relation);
            const auto object_vec = concept_vectors_.at(triple.object);
            const HDV triple_vec = hdv::triple(*subject_vec, *relation_vec, *object_vec);
            const float triple_sim = hdv::similarity(*query_vec, triple_vec);
            const float concept_sim = std::max({
                hdv::similarity(*query_vec, *subject_vec),
                hdv::similarity(*query_vec, *object_vec),
                hdv::similarity(*query_vec, *relation_vec)
            });
            const float score = 0.55f * triple_sim + 0.45f * concept_sim;
            scored.emplace_back(triple, score);
        }
        const std::size_t k = std::min(limit, scored.size());
        std::partial_sort(scored.begin(), scored.begin() + k, scored.end(),
                          [](const auto& a, const auto& b) { return a.second > b.second; });
        scored.resize(k);
        return scored;
    }

    void decay_stale(std::chrono::hours age, float rate) {
        const int64_t cutoff = now_epoch() - std::chrono::duration_cast<std::chrono::seconds>(age).count();
        std::unique_lock<std::shared_mutex> lock(mutex_);
        for (auto& entry : triples_) {
            if (entry.second.last_access < cutoff) {
                entry.second.weight = clamp_value(entry.second.weight - rate, WEIGHT_FLOOR, WEIGHT_CEILING);
            }
        }
    }

    struct MergeStats {
        std::size_t strengthened{0};
        std::size_t decayed{0};
        std::size_t merged{0};
    };

    MergeStats optimizer_pass() {
        MergeStats stats;
        std::unique_lock<std::shared_mutex> lock(mutex_);
        for (auto& entry : triples_) {
            TripleRecord& triple = entry.second;
            if (triple.access_count >= 3) {
                triple.weight = clamp_value(triple.weight + 0.05f, WEIGHT_FLOOR, WEIGHT_CEILING);
                triple.certainty = clamp_value(triple.certainty + 0.01f, CERTAINTY_FLOOR, CERTAINTY_CEILING);
                stats.strengthened += 1;
            }
            if (now_epoch() - triple.last_access > 24 * 3600) {
                triple.weight = clamp_value(triple.weight - 0.03f, WEIGHT_FLOOR, WEIGHT_CEILING);
                stats.decayed += 1;
            }
        }
        stats.merged = merge_duplicates_unlocked();
        return stats;
    }

    std::size_t prune_lowest_weight(std::size_t count) {
        std::unique_lock<std::shared_mutex> lock(mutex_);
        return prune_lowest_weight_unlocked(count);
    }

    std::vector<TripleRecord> loadable_records() const {
        return snapshot();
    }

    void load_records(const std::vector<TripleRecord>& records) {
        std::unique_lock<std::shared_mutex> lock(mutex_);
        triples_.clear();
        key_to_id_.clear();
        subject_index_.clear();
        object_index_.clear();
        relation_index_.clear();
        degree_.clear();
        concept_vectors_.clear();
        pair_affinity_.clear();
        next_id_ = 1;
        for (const TripleRecord& record : records) {
            ensure_concept_unlocked(record.subject);
            ensure_concept_unlocked(record.relation);
            ensure_concept_unlocked(record.object);
            triples_[record.id] = record;
            key_to_id_[triple_key(record.subject, record.relation, record.object)] = record.id;
            subject_index_[record.subject].push_back(record.id);
            object_index_[record.object].push_back(record.id);
            relation_index_[record.relation].push_back(record.id);
            degree_[record.subject] += 1;
            degree_[record.object] += 1;
            hebbian_reinforce_unlocked(record.subject, record.object);
            next_id_ = std::max(next_id_, record.id + 1);
        }
    }

private:
    float local_entropy_unlocked(const std::string& cname) const {
        std::unordered_map<std::string, double> buckets;
        double total_weight = 0.0;
        auto accumulate_from = [&](const auto& index) {
            auto it = index.find(cname);
            if (it == index.end()) {
                return;
            }
            for (int64_t id : it->second) {
                auto triple_it = triples_.find(id);
                if (triple_it == triples_.end()) {
                    continue;
                }
                const TripleRecord& triple = triple_it->second;
                const std::string bucket = triple.relation + "->" +
                    (triple.subject == cname ? triple.object : triple.subject);
                buckets[bucket] += triple.weight * triple.certainty;
                total_weight += triple.weight * triple.certainty;
            }
        };
        accumulate_from(subject_index_);
        accumulate_from(object_index_);
        if (buckets.empty() || total_weight <= 1e-9) {
            return 2.5f;
        }
        double entropy = 0.0;
        for (const auto& entry : buckets) {
            const double p = entry.second / total_weight;
            if (p > 1e-12) {
                entropy -= p * std::log2(p);
            }
        }
        auto degree_it = degree_.find(cname);
        const int degree = degree_it == degree_.end() ? 0 : degree_it->second;
        if (degree < 3) {
            entropy += static_cast<double>(3 - degree) * 0.4;
        }
        return static_cast<float>(entropy);
    }

    void ensure_concept_unlocked(const std::string& cname) {
        if (concept_vectors_.count(cname) == 0U) {
            concept_vectors_[cname] = encoder_.encode(cname);
        }
    }

    void hebbian_reinforce_unlocked(const std::string& left, const std::string& right) {
        const std::string forward = left + "\x1f" + right;
        const std::string reverse = right + "\x1f" + left;
        pair_affinity_[forward] = clamp_value(pair_affinity_[forward] + 0.04f, 0.0f, 1.0f);
        pair_affinity_[reverse] = clamp_value(pair_affinity_[reverse] + 0.04f, 0.0f, 1.0f);
    }

    std::size_t merge_duplicates_unlocked() {
        std::size_t merged = 0;
        std::unordered_map<std::string, std::vector<int64_t>> by_relation;
        for (const auto& entry : triples_) {
            by_relation[entry.second.relation].push_back(entry.first);
        }
        std::vector<int64_t> removals;
        for (auto& bucket : by_relation) {
            auto& ids = bucket.second;
            for (std::size_t i = 0; i < ids.size(); ++i) {
                auto a_it = triples_.find(ids[i]);
                if (a_it == triples_.end()) {
                    continue;
                }
                for (std::size_t j = i + 1; j < ids.size(); ++j) {
                    auto b_it = triples_.find(ids[j]);
                    if (b_it == triples_.end()) {
                        continue;
                    }
                    const float subject_sim = hdv::similarity(*concept_vectors_.at(a_it->second.subject),
                                                              *concept_vectors_.at(b_it->second.subject));
                    const float object_sim = hdv::similarity(*concept_vectors_.at(a_it->second.object),
                                                             *concept_vectors_.at(b_it->second.object));
                    if (subject_sim > 0.95f && object_sim > 0.95f) {
                        a_it->second.weight = clamp_value(a_it->second.weight + b_it->second.weight, WEIGHT_FLOOR, WEIGHT_CEILING);
                        a_it->second.certainty = clamp_value((a_it->second.certainty + b_it->second.certainty) * 0.5f,
                                                             CERTAINTY_FLOOR, CERTAINTY_CEILING);
                        a_it->second.sources.insert(b_it->second.sources.begin(), b_it->second.sources.end());
                        removals.push_back(b_it->first);
                        merged += 1;
                    }
                }
            }
        }
        for (int64_t id : removals) {
            remove_by_id_unlocked(id);
        }
        return merged;
    }

    void remove_by_id_unlocked(int64_t id) {
        auto it = triples_.find(id);
        if (it == triples_.end()) {
            return;
        }
        key_to_id_.erase(triple_key(it->second.subject, it->second.relation, it->second.object));
        erase_index(subject_index_[it->second.subject], id);
        erase_index(object_index_[it->second.object], id);
        erase_index(relation_index_[it->second.relation], id);
        degree_[it->second.subject] = std::max(0, degree_[it->second.subject] - 1);
        degree_[it->second.object] = std::max(0, degree_[it->second.object] - 1);
        triples_.erase(it);
    }

    std::size_t prune_lowest_weight_unlocked(std::size_t count) {
        std::vector<std::pair<float, int64_t>> ranked;
        ranked.reserve(triples_.size());
        for (const auto& entry : triples_) {
            ranked.emplace_back(entry.second.weight * entry.second.certainty, entry.first);
        }
        const std::size_t k = std::min(count, ranked.size());
        std::partial_sort(ranked.begin(), ranked.begin() + k, ranked.end(),
                          [](const auto& a, const auto& b) { return a.first < b.first; });
        for (std::size_t i = 0; i < k; ++i) {
            remove_by_id_unlocked(ranked[i].second);
        }
        return k;
    }

    static void erase_index(std::vector<int64_t>& values, int64_t id) {
        values.erase(std::remove(values.begin(), values.end(), id), values.end());
    }

    SymbolEncoder& encoder_;
    mutable std::shared_mutex mutex_;
    int64_t next_id_{1};
    std::unordered_map<int64_t, TripleRecord> triples_;
    std::unordered_map<std::string, int64_t> key_to_id_;
    std::unordered_map<std::string, std::vector<int64_t>> subject_index_;
    std::unordered_map<std::string, std::vector<int64_t>> object_index_;
    std::unordered_map<std::string, std::vector<int64_t>> relation_index_;
    std::unordered_map<std::string, int> degree_;
    std::unordered_map<std::string, std::shared_ptr<const HDV>> concept_vectors_;
    std::unordered_map<std::string, float> pair_affinity_;
};

struct SearchResult {
    std::string topic;
    std::string text;
    std::string source_url;
    double score{0.0};
};

class SQLiteError : public std::runtime_error {
public:
    explicit SQLiteError(const std::string& message)
        : std::runtime_error(message) {}
};

void check_sqlite(int rc, sqlite3* db, const std::string& context) {
    if (rc == SQLITE_OK || rc == SQLITE_DONE || rc == SQLITE_ROW) {
        return;
    }
    std::string message = context + ": ";
    if (db != nullptr) {
        message += sqlite3_errmsg(db);
    } else {
        message += "unknown sqlite error";
    }
    throw SQLiteError(message);
}

std::string join_sources(const std::set<std::string>& sources) {
    return join_strings(std::vector<std::string>(sources.begin(), sources.end()), "|");
}

std::set<std::string> split_sources(const std::string& value) {
    std::set<std::string> out;
    std::string current;
    for (char c : value) {
        if (c == '|') {
            if (!current.empty()) {
                out.insert(current);
            }
            current.clear();
        } else {
            current.push_back(c);
        }
    }
    if (!current.empty()) {
        out.insert(current);
    }
    return out;
}

class OmegaMemory {
public:
    explicit OmegaMemory(const std::string& path)
        : path_(path) {
        open();
        create_schema();
    }

    ~OmegaMemory() {
        if (db_ != nullptr) {
            sqlite3_close(db_);
        }
    }

    std::string path() const {
        return path_;
    }

    void load_mesh(KnowledgeMesh& mesh) {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        const char* sql =
            "SELECT id, subject, relation, object, weight, certainty, contradiction_flag, "
            "quarantined, first_seen, last_seen, last_access, access_count, temporal, sources "
            "FROM triples ORDER BY id ASC;";
        check_sqlite(sqlite3_prepare_v2(db_, sql, -1, &stmt, nullptr), db_, "prepare load mesh");
        std::vector<TripleRecord> records;
        while (sqlite3_step(stmt) == SQLITE_ROW) {
            TripleRecord record;
            record.id = sqlite3_column_int64(stmt, 0);
            record.subject = text_column(stmt, 1);
            record.relation = text_column(stmt, 2);
            record.object = text_column(stmt, 3);
            record.weight = static_cast<float>(sqlite3_column_double(stmt, 4));
            record.certainty = static_cast<float>(sqlite3_column_double(stmt, 5));
            record.contradiction_flag = sqlite3_column_int(stmt, 6) != 0;
            record.quarantined = sqlite3_column_int(stmt, 7) != 0;
            record.first_seen = sqlite3_column_int64(stmt, 8);
            record.last_seen = sqlite3_column_int64(stmt, 9);
            record.last_access = sqlite3_column_int64(stmt, 10);
            record.access_count = static_cast<uint64_t>(sqlite3_column_int64(stmt, 11));
            record.temporal = parse_temporal(text_column(stmt, 12));
            record.sources = split_sources(text_column(stmt, 13));
            records.push_back(record);
        }
        sqlite3_finalize(stmt);
        mesh.load_records(records);
    }

    void persist_triple(const TripleRecord& record) {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        const char* sql =
            "INSERT INTO triples(id, subject, relation, object, weight, certainty, contradiction_flag, quarantined, "
            "first_seen, last_seen, last_access, access_count, temporal, sources) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?) "
            "ON CONFLICT(id) DO UPDATE SET "
            "subject=excluded.subject, relation=excluded.relation, object=excluded.object, weight=excluded.weight, "
            "certainty=excluded.certainty, contradiction_flag=excluded.contradiction_flag, quarantined=excluded.quarantined, "
            "first_seen=excluded.first_seen, last_seen=excluded.last_seen, last_access=excluded.last_access, "
            "access_count=excluded.access_count, temporal=excluded.temporal, sources=excluded.sources;";
        check_sqlite(sqlite3_prepare_v2(db_, sql, -1, &stmt, nullptr), db_, "prepare persist triple");
        sqlite3_bind_int64(stmt, 1, record.id);
        sqlite3_bind_text(stmt, 2, record.subject.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 3, record.relation.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 4, record.object.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_double(stmt, 5, record.weight);
        sqlite3_bind_double(stmt, 6, record.certainty);
        sqlite3_bind_int(stmt, 7, record.contradiction_flag ? 1 : 0);
        sqlite3_bind_int(stmt, 8, record.quarantined ? 1 : 0);
        sqlite3_bind_int64(stmt, 9, record.first_seen);
        sqlite3_bind_int64(stmt, 10, record.last_seen);
        sqlite3_bind_int64(stmt, 11, record.last_access);
        sqlite3_bind_int64(stmt, 12, static_cast<sqlite3_int64>(record.access_count));
        const std::string temporal = temporal_name(record.temporal);
        const std::string sources = join_sources(record.sources);
        sqlite3_bind_text(stmt, 13, temporal.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 14, sources.c_str(), -1, SQLITE_TRANSIENT);
        step_with_retry(stmt, "persist triple");
        sqlite3_finalize(stmt);
    }

    void delete_triple(int64_t id) {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_, "DELETE FROM triples WHERE id=?;", -1, &stmt, nullptr), db_, "prepare delete triple");
        sqlite3_bind_int64(stmt, 1, id);
        step_with_retry(stmt, "delete triple");
        sqlite3_finalize(stmt);
    }

    bool topic_exists(const std::string& topic) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_, "SELECT 1 FROM topics WHERE name=?;", -1, &stmt, nullptr), db_, "prepare topic exists");
        sqlite3_bind_text(stmt, 1, topic.c_str(), -1, SQLITE_TRANSIENT);
        const bool exists = sqlite3_step(stmt) == SQLITE_ROW;
        sqlite3_finalize(stmt);
        return exists;
    }

    std::string topic_category(const std::string& topic) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_, "SELECT category FROM topics WHERE name=?;", -1, &stmt, nullptr), db_, "prepare topic category");
        sqlite3_bind_text(stmt, 1, topic.c_str(), -1, SQLITE_TRANSIENT);
        std::string result = "general";
        if (sqlite3_step(stmt) == SQLITE_ROW) {
            result = text_column(stmt, 0);
        }
        sqlite3_finalize(stmt);
        return result;
    }

    void store_page(const std::string& topic,
                    const std::string& title,
                    const std::string& summary,
                    const std::string& url,
                    const std::vector<std::string>& links,
                    const std::string& category) {
        std::lock_guard<std::mutex> lock(mutex_);
        execute("BEGIN IMMEDIATE;");
        sqlite3_stmt* delete_stmt = nullptr;
        sqlite3_stmt* topic_stmt = nullptr;
        sqlite3_stmt* sentence_stmt = nullptr;
        sqlite3_stmt* connection_stmt = nullptr;
        try {
            check_sqlite(sqlite3_prepare_v2(db_, "DELETE FROM sentences WHERE topic=?;", -1, &delete_stmt, nullptr), db_, "prepare delete sentences");
            sqlite3_bind_text(delete_stmt, 1, topic.c_str(), -1, SQLITE_TRANSIENT);
            step_with_retry(delete_stmt, "delete sentences");
            sqlite3_finalize(delete_stmt);
            delete_stmt = nullptr;

            const char* topic_sql =
                "INSERT INTO topics(name, title, summary, url, category, last_crawled, last_yield) "
                "VALUES(?,?,?,?,?,?,?) "
                "ON CONFLICT(name) DO UPDATE SET title=excluded.title, summary=excluded.summary, url=excluded.url, "
                "category=excluded.category, last_crawled=excluded.last_crawled, last_yield=excluded.last_yield;";
            check_sqlite(sqlite3_prepare_v2(db_, topic_sql, -1, &topic_stmt, nullptr), db_, "prepare store topic");
            sqlite3_bind_text(topic_stmt, 1, topic.c_str(), -1, SQLITE_TRANSIENT);
            sqlite3_bind_text(topic_stmt, 2, title.c_str(), -1, SQLITE_TRANSIENT);
            sqlite3_bind_text(topic_stmt, 3, summary.c_str(), -1, SQLITE_TRANSIENT);
            sqlite3_bind_text(topic_stmt, 4, url.c_str(), -1, SQLITE_TRANSIENT);
            sqlite3_bind_text(topic_stmt, 5, category.c_str(), -1, SQLITE_TRANSIENT);
            sqlite3_bind_int64(topic_stmt, 6, now_epoch());
            sqlite3_bind_double(topic_stmt, 7, 0.0);
            step_with_retry(topic_stmt, "store topic");
            sqlite3_finalize(topic_stmt);
            topic_stmt = nullptr;

            check_sqlite(sqlite3_prepare_v2(db_,
                "INSERT INTO sentences(topic, text, source_url, chunk_id, score) VALUES(?,?,?,?,?);",
                -1, &sentence_stmt, nullptr), db_, "prepare store sentences");
            const auto sentences = split_sentences(summary);
            for (std::size_t i = 0; i < sentences.size(); ++i) {
                const std::string trimmed = trim_copy(sentences[i]);
                if (trimmed.size() < 24) {
                    continue;
                }
                sqlite3_bind_text(sentence_stmt, 1, topic.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_text(sentence_stmt, 2, trimmed.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_text(sentence_stmt, 3, url.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_int(sentence_stmt, 4, static_cast<int>(i));
                sqlite3_bind_double(sentence_stmt, 5, 1.0 / (1.0 + static_cast<double>(i) * 0.1));
                step_with_retry(sentence_stmt, "store sentence");
                sqlite3_reset(sentence_stmt);
                sqlite3_clear_bindings(sentence_stmt);
            }
            sqlite3_finalize(sentence_stmt);
            sentence_stmt = nullptr;

            const char* connection_sql =
                "INSERT INTO connections(from_topic, to_topic, weight, last_seen) VALUES(?,?,1.0,?) "
                "ON CONFLICT(from_topic, to_topic) DO UPDATE SET weight=weight+1.0, last_seen=excluded.last_seen;";
            check_sqlite(sqlite3_prepare_v2(db_, connection_sql, -1, &connection_stmt, nullptr), db_, "prepare store connections");
            for (const std::string& link : links) {
                sqlite3_bind_text(connection_stmt, 1, topic.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_text(connection_stmt, 2, link.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_int64(connection_stmt, 3, now_epoch());
                step_with_retry(connection_stmt, "store connection");
                sqlite3_reset(connection_stmt);
                sqlite3_clear_bindings(connection_stmt);
            }
            sqlite3_finalize(connection_stmt);
            connection_stmt = nullptr;

            execute("COMMIT;");
        } catch (...) {
            if (delete_stmt != nullptr) {
                sqlite3_finalize(delete_stmt);
            }
            if (topic_stmt != nullptr) {
                sqlite3_finalize(topic_stmt);
            }
            if (sentence_stmt != nullptr) {
                sqlite3_finalize(sentence_stmt);
            }
            if (connection_stmt != nullptr) {
                sqlite3_finalize(connection_stmt);
            }
            try {
                execute("ROLLBACK;");
            } catch (...) {
            }
            throw;
        }
    }

    std::vector<SearchResult> search(const std::string& query, int limit = static_cast<int>(FTS_LIMIT)) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        const char* sql =
            "SELECT topic, text, source_url, score FROM sentences "
            "WHERE sentences MATCH ? ORDER BY score DESC LIMIT ?;";
        check_sqlite(sqlite3_prepare_v2(db_, sql, -1, &stmt, nullptr), db_, "prepare search");
        const std::string sanitized = sanitize_fts_query(query);
        sqlite3_bind_text(stmt, 1, sanitized.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 2, limit);
        std::vector<SearchResult> out;
        while (sqlite3_step(stmt) == SQLITE_ROW) {
            SearchResult result;
            result.topic = text_column(stmt, 0);
            result.text = text_column(stmt, 1);
            result.source_url = text_column(stmt, 2);
            result.score = sqlite3_column_double(stmt, 3);
            out.push_back(result);
        }
        sqlite3_finalize(stmt);
        return out;
    }

    std::vector<std::string> related_topics(const std::string& topic, int limit = 10) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_,
            "SELECT to_topic FROM connections WHERE from_topic=? ORDER BY weight DESC LIMIT ?;",
            -1, &stmt, nullptr), db_, "prepare related topics");
        sqlite3_bind_text(stmt, 1, topic.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 2, limit);
        std::vector<std::string> out;
        while (sqlite3_step(stmt) == SQLITE_ROW) {
            out.push_back(text_column(stmt, 0));
        }
        sqlite3_finalize(stmt);
        return out;
    }

    void log_query(const std::string& query, int result_count, double confidence, bool resolved) {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_,
            "INSERT INTO query_log(query, result_count, confidence, answered_at, resolved) VALUES(?,?,?,?,?);",
            -1, &stmt, nullptr), db_, "prepare log query");
        sqlite3_bind_text(stmt, 1, query.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 2, result_count);
        sqlite3_bind_double(stmt, 3, confidence);
        sqlite3_bind_int64(stmt, 4, now_epoch());
        sqlite3_bind_int(stmt, 5, resolved ? 1 : 0);
        step_with_retry(stmt, "log query");
        sqlite3_finalize(stmt);
    }

    int unresolved_query_count() const {
        return static_cast<int>(scalar_int("SELECT COUNT(*) FROM query_log WHERE resolved=0;"));
    }

    int total_query_count() const {
        return static_cast<int>(scalar_int("SELECT COUNT(*) FROM query_log;"));
    }

    int sentence_count() const {
        return static_cast<int>(scalar_int("SELECT COUNT(*) FROM sentences;"));
    }

    int topic_count() const {
        return static_cast<int>(scalar_int("SELECT COUNT(*) FROM topics;"));
    }

    int triple_count() const {
        return static_cast<int>(scalar_int("SELECT COUNT(*) FROM triples;"));
    }

    void rewrite_triples(const std::vector<TripleRecord>& records) {
        std::lock_guard<std::mutex> lock(mutex_);
        execute("BEGIN IMMEDIATE;");
        sqlite3_stmt* stmt = nullptr;
        try {
            execute("DELETE FROM triples;");
            const char* sql =
                "INSERT INTO triples(id, subject, relation, object, weight, certainty, contradiction_flag, quarantined, "
                "first_seen, last_seen, last_access, access_count, temporal, sources) "
                "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?);";
            check_sqlite(sqlite3_prepare_v2(db_, sql, -1, &stmt, nullptr), db_, "prepare rewrite triples");
            for (const TripleRecord& record : records) {
                sqlite3_bind_int64(stmt, 1, record.id);
                sqlite3_bind_text(stmt, 2, record.subject.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_text(stmt, 3, record.relation.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_text(stmt, 4, record.object.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_double(stmt, 5, record.weight);
                sqlite3_bind_double(stmt, 6, record.certainty);
                sqlite3_bind_int(stmt, 7, record.contradiction_flag ? 1 : 0);
                sqlite3_bind_int(stmt, 8, record.quarantined ? 1 : 0);
                sqlite3_bind_int64(stmt, 9, record.first_seen);
                sqlite3_bind_int64(stmt, 10, record.last_seen);
                sqlite3_bind_int64(stmt, 11, record.last_access);
                sqlite3_bind_int64(stmt, 12, static_cast<sqlite3_int64>(record.access_count));
                const std::string temporal = temporal_name(record.temporal);
                const std::string sources = join_sources(record.sources);
                sqlite3_bind_text(stmt, 13, temporal.c_str(), -1, SQLITE_TRANSIENT);
                sqlite3_bind_text(stmt, 14, sources.c_str(), -1, SQLITE_TRANSIENT);
                step_with_retry(stmt, "rewrite triple");
                sqlite3_reset(stmt);
                sqlite3_clear_bindings(stmt);
            }
            sqlite3_finalize(stmt);
            stmt = nullptr;
            execute("COMMIT;");
        } catch (...) {
            if (stmt != nullptr) {
                sqlite3_finalize(stmt);
            }
            try {
                execute("ROLLBACK;");
            } catch (...) {
            }
            throw;
        }
    }

    void record_crawl(const std::string& topic,
                      int pages_fetched,
                      int triples_added,
                      double entropy_before,
                      double entropy_after,
                      double duration_seconds) {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_,
            "INSERT INTO crawl_events(topic, pages_fetched, triples_added, entropy_before, entropy_after, duration, crawled_at) "
            "VALUES(?,?,?,?,?,?,?);", -1, &stmt, nullptr), db_, "prepare record crawl");
        sqlite3_bind_text(stmt, 1, topic.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int(stmt, 2, pages_fetched);
        sqlite3_bind_int(stmt, 3, triples_added);
        sqlite3_bind_double(stmt, 4, entropy_before);
        sqlite3_bind_double(stmt, 5, entropy_after);
        sqlite3_bind_double(stmt, 6, duration_seconds);
        sqlite3_bind_int64(stmt, 7, now_epoch());
        step_with_retry(stmt, "record crawl");
        sqlite3_finalize(stmt);
    }

    void vacuum() {
        std::lock_guard<std::mutex> lock(mutex_);
        execute("VACUUM;");
    }

    uintmax_t file_size_bytes() const {
        std::error_code ec;
        const uintmax_t size = fs::exists(path_, ec) ? fs::file_size(path_, ec) : 0;
        return ec ? 0 : size;
    }

private:
    void open() {
        if (sqlite3_open(path_.c_str(), &db_) != SQLITE_OK) {
            throw SQLiteError("Failed to open " + path_);
        }
        sqlite3_busy_timeout(db_, 5000);
    }

    void execute(const std::string& sql) {
        char* error = nullptr;
        const int rc = sqlite3_exec(db_, sql.c_str(), nullptr, nullptr, &error);
        if (rc != SQLITE_OK) {
            const std::string message = error == nullptr ? "sqlite exec failed" : error;
            if (error != nullptr) {
                sqlite3_free(error);
            }
            throw SQLiteError(message);
        }
    }

    void create_schema() {
        execute("PRAGMA journal_mode=WAL;");
        execute("PRAGMA synchronous=NORMAL;");
        execute("PRAGMA cache_size=-65536;");
        execute(
            "CREATE VIRTUAL TABLE IF NOT EXISTS sentences USING fts5("
            "topic, text, source_url UNINDEXED, chunk_id UNINDEXED, score UNINDEXED,"
            "tokenize='porter unicode61');");
        execute(
            "CREATE TABLE IF NOT EXISTS topics("
            "name TEXT PRIMARY KEY, title TEXT, summary TEXT, url TEXT, category TEXT,"
            "last_crawled INTEGER, last_yield REAL DEFAULT 0.0);");
        execute(
            "CREATE TABLE IF NOT EXISTS connections("
            "from_topic TEXT, to_topic TEXT, weight REAL DEFAULT 1.0, last_seen INTEGER,"
            "PRIMARY KEY(from_topic, to_topic));");
        execute(
            "CREATE TABLE IF NOT EXISTS triples("
            "id INTEGER PRIMARY KEY, subject TEXT, relation TEXT, object TEXT,"
            "weight REAL, certainty REAL, contradiction_flag INTEGER, quarantined INTEGER,"
            "first_seen INTEGER, last_seen INTEGER, last_access INTEGER, access_count INTEGER,"
            "temporal TEXT, sources TEXT, UNIQUE(subject, relation, object));");
        execute(
            "CREATE TABLE IF NOT EXISTS query_log("
            "id INTEGER PRIMARY KEY AUTOINCREMENT, query TEXT, result_count INTEGER,"
            "confidence REAL, answered_at INTEGER, resolved INTEGER);");
        execute(
            "CREATE TABLE IF NOT EXISTS crawl_events("
            "id INTEGER PRIMARY KEY AUTOINCREMENT, topic TEXT, pages_fetched INTEGER,"
            "triples_added INTEGER, entropy_before REAL, entropy_after REAL,"
            "duration REAL, crawled_at INTEGER);");
    }

    static std::string sanitize_fts_query(const std::string& query) {
        std::ostringstream oss;
        for (char c : query) {
            if (std::isalnum(static_cast<unsigned char>(c)) || std::isspace(static_cast<unsigned char>(c))) {
                oss << c;
            }
        }
        const std::string trimmed = trim_copy(oss.str());
        return trimmed.empty() ? "knowledge" : trimmed;
    }

    static std::string text_column(sqlite3_stmt* stmt, int column) {
        const unsigned char* text = sqlite3_column_text(stmt, column);
        return text == nullptr ? std::string() : reinterpret_cast<const char*>(text);
    }

    static TemporalState parse_temporal(const std::string& value) {
        const std::string upper = upper_copy(value);
        if (upper == "PAST") {
            return TemporalState::Past;
        }
        if (upper == "FUTURE") {
            return TemporalState::Future;
        }
        if (upper == "UNKNOWN") {
            return TemporalState::Unknown;
        }
        return TemporalState::Present;
    }

    void step_with_retry(sqlite3_stmt* stmt, const std::string& context) {
        for (int attempt = 0; attempt < 5; ++attempt) {
            const int rc = sqlite3_step(stmt);
            if (rc == SQLITE_DONE || rc == SQLITE_ROW) {
                return;
            }
            if (rc != SQLITE_BUSY && rc != SQLITE_LOCKED) {
                check_sqlite(rc, db_, context);
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(50 * (attempt + 1)));
        }
        check_sqlite(SQLITE_BUSY, db_, context);
    }

    int64_t scalar_int(const std::string& sql) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_, sql.c_str(), -1, &stmt, nullptr), db_, "prepare scalar");
        int64_t value = 0;
        if (sqlite3_step(stmt) == SQLITE_ROW) {
            value = sqlite3_column_int64(stmt, 0);
        }
        sqlite3_finalize(stmt);
        return value;
    }

    std::string path_;
    mutable std::mutex mutex_;
    sqlite3* db_{nullptr};
};

struct HypothesisRecord {
    int64_t id{0};
    std::string subject;
    std::string relation;
    std::string object;
    double confidence{0.0};
    std::string status;
    std::string trigger_concept;
    std::string evidence;
    int64_t generated_at{0};
    int64_t verified_at{0};
    int64_t promoted_at{0};
    int64_t refuted_at{0};
};

class HypothesisStore {
public:
    explicit HypothesisStore(const std::string& path)
        : path_(path) {
        if (sqlite3_open(path_.c_str(), &db_) != SQLITE_OK) {
            throw SQLiteError("Failed to open " + path_);
        }
        sqlite3_busy_timeout(db_, 5000);
        execute("PRAGMA journal_mode=WAL;");
        execute("PRAGMA synchronous=NORMAL;");
        execute(
            "CREATE TABLE IF NOT EXISTS hypotheses("
            "id INTEGER PRIMARY KEY AUTOINCREMENT, subject TEXT, relation TEXT, object TEXT,"
            "confidence REAL, status TEXT, trigger_concept TEXT, evidence TEXT,"
            "generated_at INTEGER, verified_at INTEGER, promoted_at INTEGER, refuted_at INTEGER,"
            "UNIQUE(subject, relation, object));");
    }

    ~HypothesisStore() {
        if (db_ != nullptr) {
            sqlite3_close(db_);
        }
    }

    std::optional<int64_t> upsert_candidate(const HypothesisRecord& record) {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        const char* sql =
            "INSERT INTO hypotheses(subject, relation, object, confidence, status, trigger_concept, evidence, generated_at, verified_at, promoted_at, refuted_at) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?) "
            "ON CONFLICT(subject, relation, object) DO UPDATE SET "
            "confidence=excluded.confidence, status=excluded.status, trigger_concept=excluded.trigger_concept, evidence=excluded.evidence;";
        check_sqlite(sqlite3_prepare_v2(db_, sql, -1, &stmt, nullptr), db_, "prepare hypothesis upsert");
        bind_record(stmt, record);
        int rc = sqlite3_step(stmt);
        sqlite3_finalize(stmt);
        check_sqlite(rc, db_, "upsert hypothesis");

        sqlite3_stmt* select_stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_,
            "SELECT id FROM hypotheses WHERE subject=? AND relation=? AND object=?;",
            -1, &select_stmt, nullptr), db_, "prepare hypothesis lookup");
        sqlite3_bind_text(select_stmt, 1, record.subject.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(select_stmt, 2, record.relation.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(select_stmt, 3, record.object.c_str(), -1, SQLITE_TRANSIENT);
        std::optional<int64_t> id;
        if (sqlite3_step(select_stmt) == SQLITE_ROW) {
            id = sqlite3_column_int64(select_stmt, 0);
        }
        sqlite3_finalize(select_stmt);
        return id;
    }

    std::optional<HypothesisRecord> oldest_candidate() const {
        return select_one("SELECT id, subject, relation, object, confidence, status, trigger_concept, evidence, generated_at, verified_at, promoted_at, refuted_at "
                          "FROM hypotheses WHERE status='CANDIDATE' ORDER BY generated_at ASC LIMIT 1;");
    }

    void update_status(int64_t id, const std::string& status, const std::string& evidence) {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_,
            "UPDATE hypotheses SET status=?, evidence=?, verified_at=?, "
            "promoted_at=CASE WHEN ?='PROMOTED' THEN ? ELSE promoted_at END, "
            "refuted_at=CASE WHEN ?='REFUTED' THEN ? ELSE refuted_at END "
            "WHERE id=?;", -1, &stmt, nullptr), db_, "prepare hypothesis status");
        const int64_t now = now_epoch();
        sqlite3_bind_text(stmt, 1, status.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 2, evidence.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int64(stmt, 3, now);
        sqlite3_bind_text(stmt, 4, status.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int64(stmt, 5, now);
        sqlite3_bind_text(stmt, 6, status.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int64(stmt, 7, now);
        sqlite3_bind_int64(stmt, 8, id);
        const int rc = sqlite3_step(stmt);
        sqlite3_finalize(stmt);
        check_sqlite(rc, db_, "update hypothesis status");
    }

    std::vector<HypothesisRecord> top(std::size_t limit) const {
        return select_many(
            "SELECT id, subject, relation, object, confidence, status, trigger_concept, evidence, "
            "generated_at, verified_at, promoted_at, refuted_at "
            "FROM hypotheses ORDER BY confidence DESC, generated_at DESC LIMIT " + std::to_string(limit) + ";");
    }

    std::size_t count_active() const {
        return static_cast<std::size_t>(scalar_int("SELECT COUNT(*) FROM hypotheses WHERE status IN ('CANDIDATE','PROMOTED');"));
    }

private:
    void execute(const std::string& sql) {
        char* error = nullptr;
        const int rc = sqlite3_exec(db_, sql.c_str(), nullptr, nullptr, &error);
        if (rc != SQLITE_OK) {
            const std::string message = error == nullptr ? "sqlite exec failed" : error;
            if (error != nullptr) {
                sqlite3_free(error);
            }
            throw SQLiteError(message);
        }
    }

    void bind_record(sqlite3_stmt* stmt, const HypothesisRecord& record) {
        sqlite3_bind_text(stmt, 1, record.subject.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 2, record.relation.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 3, record.object.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_double(stmt, 4, record.confidence);
        sqlite3_bind_text(stmt, 5, record.status.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 6, record.trigger_concept.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 7, record.evidence.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int64(stmt, 8, record.generated_at);
        sqlite3_bind_int64(stmt, 9, record.verified_at);
        sqlite3_bind_int64(stmt, 10, record.promoted_at);
        sqlite3_bind_int64(stmt, 11, record.refuted_at);
    }

    std::optional<HypothesisRecord> select_one(const std::string& sql) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_, sql.c_str(), -1, &stmt, nullptr), db_, "prepare hypothesis select one");
        HypothesisRecord record;
        if (sqlite3_step(stmt) == SQLITE_ROW) {
            record = from_stmt(stmt);
            sqlite3_finalize(stmt);
            return record;
        }
        sqlite3_finalize(stmt);
        return std::nullopt;
    }

    std::vector<HypothesisRecord> select_many(const std::string& sql) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_, sql.c_str(), -1, &stmt, nullptr), db_, "prepare hypothesis select many");
        std::vector<HypothesisRecord> out;
        while (sqlite3_step(stmt) == SQLITE_ROW) {
            out.push_back(from_stmt(stmt));
        }
        sqlite3_finalize(stmt);
        return out;
    }

    int64_t scalar_int(const std::string& sql) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_, sql.c_str(), -1, &stmt, nullptr), db_, "prepare hypothesis scalar");
        int64_t value = 0;
        if (sqlite3_step(stmt) == SQLITE_ROW) {
            value = sqlite3_column_int64(stmt, 0);
        }
        sqlite3_finalize(stmt);
        return value;
    }

    static std::string col(sqlite3_stmt* stmt, int index) {
        const unsigned char* text = sqlite3_column_text(stmt, index);
        return text == nullptr ? std::string() : reinterpret_cast<const char*>(text);
    }

    static HypothesisRecord from_stmt(sqlite3_stmt* stmt) {
        HypothesisRecord record;
        record.id = sqlite3_column_int64(stmt, 0);
        record.subject = col(stmt, 1);
        record.relation = col(stmt, 2);
        record.object = col(stmt, 3);
        record.confidence = sqlite3_column_double(stmt, 4);
        record.status = col(stmt, 5);
        record.trigger_concept = col(stmt, 6);
        record.evidence = col(stmt, 7);
        record.generated_at = sqlite3_column_int64(stmt, 8);
        record.verified_at = sqlite3_column_int64(stmt, 9);
        record.promoted_at = sqlite3_column_int64(stmt, 10);
        record.refuted_at = sqlite3_column_int64(stmt, 11);
        return record;
    }

    std::string path_;
    mutable std::mutex mutex_;
    sqlite3* db_{nullptr};
};

class ParadoxStore {
public:
    explicit ParadoxStore(const std::string& path)
        : path_(path) {
        if (sqlite3_open(path_.c_str(), &db_) != SQLITE_OK) {
            throw SQLiteError("Failed to open " + path_);
        }
        sqlite3_busy_timeout(db_, 5000);
        execute("PRAGMA journal_mode=WAL;");
        execute("PRAGMA synchronous=NORMAL;");
        execute(
            "CREATE TABLE IF NOT EXISTS paradoxes("
            "id INTEGER PRIMARY KEY AUTOINCREMENT, subject TEXT, relation TEXT, object TEXT,"
            "confidence REAL, reason TEXT, discovered_at INTEGER);");
    }

    ~ParadoxStore() {
        if (db_ != nullptr) {
            sqlite3_close(db_);
        }
    }

    void insert(const std::string& subject,
                const std::string& relation,
                const std::string& object,
                double confidence,
                const std::string& reason) {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_,
            "INSERT INTO paradoxes(subject, relation, object, confidence, reason, discovered_at) VALUES(?,?,?,?,?,?);",
            -1, &stmt, nullptr), db_, "prepare paradox insert");
        sqlite3_bind_text(stmt, 1, subject.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 2, relation.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_text(stmt, 3, object.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_double(stmt, 4, confidence);
        sqlite3_bind_text(stmt, 5, reason.c_str(), -1, SQLITE_TRANSIENT);
        sqlite3_bind_int64(stmt, 6, now_epoch());
        const int rc = sqlite3_step(stmt);
        sqlite3_finalize(stmt);
        check_sqlite(rc, db_, "insert paradox");
    }

    std::vector<HypothesisRecord> list(std::size_t limit) const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_,
            ("SELECT id, subject, relation, object, confidence, 'PARADOX', reason, discovered_at, 0, 0, 0 "
             "FROM paradoxes ORDER BY discovered_at DESC LIMIT " + std::to_string(limit) + ";").c_str(),
            -1, &stmt, nullptr), db_, "prepare paradox list");
        std::vector<HypothesisRecord> out;
        while (sqlite3_step(stmt) == SQLITE_ROW) {
            HypothesisRecord record;
            record.id = sqlite3_column_int64(stmt, 0);
            record.subject = text_column(stmt, 1);
            record.relation = text_column(stmt, 2);
            record.object = text_column(stmt, 3);
            record.confidence = sqlite3_column_double(stmt, 4);
            record.status = "PARADOX";
            record.evidence = text_column(stmt, 6);
            record.generated_at = sqlite3_column_int64(stmt, 7);
            out.push_back(record);
        }
        sqlite3_finalize(stmt);
        return out;
    }

    std::size_t count() const {
        std::lock_guard<std::mutex> lock(mutex_);
        sqlite3_stmt* stmt = nullptr;
        check_sqlite(sqlite3_prepare_v2(db_, "SELECT COUNT(*) FROM paradoxes;", -1, &stmt, nullptr), db_, "prepare paradox count");
        std::size_t out = 0;
        if (sqlite3_step(stmt) == SQLITE_ROW) {
            out = static_cast<std::size_t>(sqlite3_column_int64(stmt, 0));
        }
        sqlite3_finalize(stmt);
        return out;
    }

private:
    static std::string text_column(sqlite3_stmt* stmt, int index) {
        const unsigned char* text = sqlite3_column_text(stmt, index);
        return text == nullptr ? std::string() : reinterpret_cast<const char*>(text);
    }

    void execute(const std::string& sql) {
        char* error = nullptr;
        const int rc = sqlite3_exec(db_, sql.c_str(), nullptr, nullptr, &error);
        if (rc != SQLITE_OK) {
            const std::string message = error == nullptr ? "sqlite exec failed" : error;
            if (error != nullptr) {
                sqlite3_free(error);
            }
            throw SQLiteError(message);
        }
    }

    std::string path_;
    mutable std::mutex mutex_;
    sqlite3* db_{nullptr};
};

struct Entity {
    std::string text;
    std::string type;
};

class NEREngine {
public:
    static std::vector<Entity> extract(const std::string& text) {
        static const std::unordered_set<std::string> stop_words = {
            "what", "is", "are", "was", "the", "and", "for", "with", "from",
            "into", "about", "explain", "show", "tell", "which", "that", "this"
        };

        std::vector<Entity> entities;
        std::vector<std::string> words = split_words(text);
        for (const std::string& word : words) {
            if (word.size() < 4 || stop_words.count(word) != 0U) {
                continue;
            }
            std::string type = "CONCEPT";
            if (std::all_of(word.begin(), word.end(), [](unsigned char c) { return std::isdigit(c); })) {
                type = "NUMBER";
            }
            entities.push_back({word, type});
        }

        std::vector<std::string> original;
        std::istringstream iss(text);
        std::string token;
        while (iss >> token) {
            token = trim_copy(token);
            while (!token.empty() && std::ispunct(static_cast<unsigned char>(token.back()))) {
                token.pop_back();
            }
            if (!token.empty()) {
                original.push_back(token);
            }
        }
        for (std::size_t i = 0; i + 1 < original.size(); ++i) {
            if (std::isupper(static_cast<unsigned char>(original[i][0])) &&
                std::isupper(static_cast<unsigned char>(original[i + 1][0]))) {
                entities.push_back({original[i] + " " + original[i + 1], "PROPER_NOUN"});
            }
        }
        return entities;
    }
};

enum class QueryIntent {
    Greeting,
    SelfQuery,
    Opinion,
    Definition,
    Comparison,
    Cause,
    Relation,
    List,
    Planning,
    Command,
    Factual,
    Unknown
};

struct ParsedQuery {
    std::string original;
    std::string resolved;
    std::string normalized;
    QueryIntent intent{QueryIntent::Factual};
    std::vector<Entity> entities;
    std::vector<std::string> relation_hints;
    bool follow_up{false};
};

struct EvidenceItem {
    std::string text;
    std::string subject;
    std::string relation;
    std::string object;
    std::string source;
    double score{0.0};
    double certainty{0.0};
    bool graph_fact{false};
};

struct AnswerPlan {
    ParsedQuery query;
    std::string skill{"general"};
    std::string direct;
    std::vector<std::string> bullets;
    std::vector<std::string> reasoning_steps;
    std::vector<std::string> caveats;
    std::vector<std::string> critic_notes;
    std::set<std::string> sources;
    std::vector<EvidenceItem> evidence;
    double confidence{0.0};
    double belief_score{0.0};
    std::string belief_label{"unverified"};
    bool verified{false};
};

class KnowledgeGrowthEngine {
public:
    static bool supported_import_extension(const fs::path& file) {
        const std::string ext = lower_copy(file.extension().string());
        return ext == ".txt" || ext == ".md" || ext == ".jsonl" || ext == ".json";
    }

    static std::string gap_instruction(const std::string& topic) {
        if (topic.empty()) {
            return "Next action: `learn <topic>`, `deep <topic>`, ya `import <path>`.";
        }
        return "Next action: `learn " + topic + "`, `deep " + topic + "`, ya `import <path>`.";
    }
};

class LocalCorpusBrain {
public:
    static std::vector<std::pair<std::string, std::string>> chunk_document(const std::string& title,
                                                                           const std::string& text,
                                                                           std::size_t sentences_per_chunk = 80) {
        std::vector<std::pair<std::string, std::string>> chunks;
        const auto sentences = split_sentences(text);
        if (sentences.empty()) {
            chunks.push_back({title, text});
            return chunks;
        }
        std::vector<std::string> current;
        int chunk_id = 1;
        for (const std::string& sentence : sentences) {
            current.push_back(sentence);
            if (current.size() >= sentences_per_chunk) {
                chunks.push_back({title + "#chunk-" + std::to_string(chunk_id++),
                                  join_strings(current, " ")});
                current.clear();
            }
        }
        if (!current.empty()) {
            chunks.push_back({title + "#chunk-" + std::to_string(chunk_id),
                              join_strings(current, " ")});
        }
        return chunks;
    }

    static std::string normalize_source_path(const fs::path& file) {
        return "file://" + file.string();
    }
};

class GPTStyleCortex {
public:
    static bool valid_mode(const std::string& mode) {
        static const std::set<std::string> allowed = {"chat", "agent", "reason", "mythos"};
        return allowed.count(mode) != 0U;
    }

    static std::string answer_shape(const std::string& mode) {
        if (mode == "agent") {
            return "direct answer -> action plan -> audit hook";
        }
        if (mode == "reason") {
            return "direct answer -> reasoning -> caveat";
        }
        if (mode == "mythos") {
            return "direct answer -> verifier note -> organism voice";
        }
        return "direct answer -> key points -> next useful action";
    }
};

class QueryParser {
public:
    static ParsedQuery parse(const std::string& raw, const std::string& resolved) {
        ParsedQuery parsed;
        parsed.original = raw;
        parsed.resolved = resolved;
        parsed.normalized = lower_copy(resolved);
        parsed.entities = NEREngine::extract(resolved);
        parsed.follow_up = contains_any(parsed.normalized, {
            "it", "this", "that", "isko", "iske", "usko", "uske", "yeh", "ye"
        });

        if (is_greeting(parsed.normalized)) {
            parsed.intent = QueryIntent::Greeting;
        } else if (contains_any(parsed.normalized, {
                       "who are you", "what are you", "tum kaun ho", "tu kaun hai",
                       "aap kaun ho", "your identity", "identity", "introduce yourself"
                   })) {
            parsed.intent = QueryIntent::SelfQuery;
        } else if (contains_any(parsed.normalized, {
                       "what do you think", "your opinion", "acha hai ya bura", "good or bad",
                       "best", "worst", "rate", "judge", "recommend"
                   })) {
            parsed.intent = QueryIntent::Opinion;
        } else if (contains_any(parsed.normalized, {
                       "plan", "steps", "roadmap", "kaise bna", "kaise bana",
                       "how to build", "how should i"
                   })) {
            parsed.intent = QueryIntent::Planning;
        } else if (contains_any(parsed.normalized, {
                       "what is", "who is", "kya hai", "kaun hai", "define", "meaning",
                       "explain", "samjha", "simple words"
                   })) {
            parsed.intent = QueryIntent::Definition;
            parsed.relation_hints.push_back("IS_A");
        } else if (contains_any(parsed.normalized, {
                       "compare", "difference", "versus", " vs ", "better than", "alag"
                   })) {
            parsed.intent = QueryIntent::Comparison;
        } else if (contains_any(parsed.normalized, {
                       "why", "kyun", "kaaran", "reason", "cause", "because"
                   })) {
            parsed.intent = QueryIntent::Cause;
            parsed.relation_hints.push_back("CAUSED_BY");
        } else if (contains_any(parsed.normalized, {
                       "relation", "connected", "link", "between", "ka relation",
                       "related to", "belongs to", "part of"
                   })) {
            parsed.intent = QueryIntent::Relation;
            parsed.relation_hints.push_back("RELATES_TO");
            parsed.relation_hints.push_back("PART_OF");
        } else if (contains_any(parsed.normalized, {
                       "list", "examples", "types", "name some", "batao sab"
                   })) {
            parsed.intent = QueryIntent::List;
        } else if (trim_copy(parsed.normalized).empty()) {
            parsed.intent = QueryIntent::Unknown;
        } else {
            parsed.intent = QueryIntent::Factual;
        }
        return parsed;
    }

    static std::string name(QueryIntent intent) {
        switch (intent) {
            case QueryIntent::Greeting: return "GREETING";
            case QueryIntent::SelfQuery: return "SELF_QUERY";
            case QueryIntent::Opinion: return "OPINION";
            case QueryIntent::Definition: return "DEFINITION";
            case QueryIntent::Comparison: return "COMPARISON";
            case QueryIntent::Cause: return "CAUSE";
            case QueryIntent::Relation: return "RELATION";
            case QueryIntent::List: return "LIST";
            case QueryIntent::Planning: return "PLANNING";
            case QueryIntent::Command: return "COMMAND";
            case QueryIntent::Unknown: return "UNKNOWN";
            case QueryIntent::Factual:
            default: return "FACTUAL";
        }
    }

private:
    static bool contains_any(const std::string& text, const std::vector<std::string>& needles) {
        for (const std::string& needle : needles) {
            if (text.find(needle) != std::string::npos) {
                return true;
            }
        }
        return false;
    }

    static bool is_greeting(const std::string& text) {
        const std::string q = trim_copy(text);
        static const std::vector<std::string> greetings = {
            "hi", "hello", "hey", "namaste", "namaskar", "good morning",
            "good afternoon", "good evening", "yo"
        };
        for (const std::string& greeting : greetings) {
            if (q == greeting || q.rfind(greeting + " ", 0) == 0) {
                return true;
            }
        }
        return false;
    }
};

class SkillEngine {
public:
    static std::string route(const ParsedQuery& query) {
        const std::string q = query.normalized;
        if (query.intent == QueryIntent::Planning) {
            return "planner";
        }
        if (query.intent == QueryIntent::Relation || q.find("connect") != std::string::npos) {
            return "graph_reasoner";
        }
        if (query.intent == QueryIntent::Cause || q.find("why") != std::string::npos) {
            return "causal_reasoner";
        }
        if (contains_any(q, {"code", "cpp", "python", "function", "bug", "compile"})) {
            return "code_reasoner";
        }
        if (contains_any(q, {"calculate", "math", "+", "-", "*", "/", "percent"})) {
            return "math_skill";
        }
        if (contains_any(q, {"memory", "recall", "source", "evidence", "why"})) {
            return "memory_auditor";
        }
        if (contains_any(q, {"physics", "biology", "chemistry", "science", "quantum"})) {
            return "science_explainer";
        }
        if (query.intent == QueryIntent::Opinion) {
            return "neutral_fact_checker";
        }
        return "knowledge_chat";
    }

    static std::string describe(const std::string& skill) {
        static const std::map<std::string, std::string> descriptions = {
            {"planner", "breaks goals into verifiable local actions"},
            {"graph_reasoner", "uses concept graph paths and relations"},
            {"causal_reasoner", "looks for causes, evidence, and caveats"},
            {"code_reasoner", "answers code questions from local evidence and rules"},
            {"math_skill", "routes arithmetic/numeric questions to deterministic handling"},
            {"memory_auditor", "surfaces local memory, evidence, and sources"},
            {"science_explainer", "prefers definitions, mechanisms, and verified claims"},
            {"neutral_fact_checker", "removes judgement and returns grounded facts"},
            {"knowledge_chat", "general local-memory conversation skill"}
        };
        auto it = descriptions.find(skill);
        return it == descriptions.end() ? "general skill route" : it->second;
    }

    static std::vector<std::string> available() {
        return {
            "knowledge_chat", "planner", "graph_reasoner", "causal_reasoner",
            "code_reasoner", "math_skill", "memory_auditor", "science_explainer",
            "neutral_fact_checker"
        };
    }

private:
    static bool contains_any(const std::string& text, const std::vector<std::string>& needles) {
        for (const std::string& needle : needles) {
            if (text.find(needle) != std::string::npos) {
                return true;
            }
        }
        return false;
    }
};

class BeliefSystem {
public:
    static void apply(AnswerPlan& plan) {
        double support = 0.0;
        double certainty = 0.0;
        int graph_facts = 0;
        std::set<std::string> sources;
        for (const EvidenceItem& item : plan.evidence) {
            support = std::max(support, item.score);
            certainty = std::max(certainty, item.certainty);
            if (item.graph_fact) {
                ++graph_facts;
            }
            if (!item.source.empty()) {
                sources.insert(item.source);
            }
        }
        const double source_bonus = clamp_double(static_cast<double>(sources.size()) * 0.06, 0.0, 0.18);
        const double graph_bonus = clamp_double(static_cast<double>(graph_facts) * 0.04, 0.0, 0.12);
        plan.belief_score = clamp_double(0.52 * support + 0.36 * certainty + source_bonus + graph_bonus,
                                         0.0, 1.0);
        if (plan.belief_score >= 0.78) {
            plan.belief_label = "strong";
        } else if (plan.belief_score >= 0.55) {
            plan.belief_label = "moderate";
        } else if (plan.belief_score >= 0.35) {
            plan.belief_label = "weak";
        } else {
            plan.belief_label = "unverified";
        }
    }
};

class AnswerCritic {
public:
    static void review(AnswerPlan& plan) {
        if (trim_copy(plan.direct).size() < 18) {
            plan.critic_notes.push_back("Direct answer too short.");
        }
        if (plan.evidence.empty()) {
            plan.critic_notes.push_back("No supporting evidence attached.");
        }
        if (plan.belief_score < 0.35) {
            plan.critic_notes.push_back("Belief score below safe answer threshold.");
        }
        if (plan.query.intent != QueryIntent::Opinion && lower_copy(plan.direct).find("i think") != std::string::npos) {
            plan.critic_notes.push_back("Speculative phrasing detected.");
        }
        if (!plan.critic_notes.empty() && plan.belief_score < 0.55) {
            plan.verified = false;
            if (plan.caveats.empty()) {
                plan.caveats.push_back("Answer critic ne response ko weak mark kiya.");
            }
        }
    }
};

class StrictVerifier {
public:
    static bool verify(AnswerPlan& plan) {
        double best = 0.0;
        for (const EvidenceItem& item : plan.evidence) {
            best = std::max(best, item.score * 0.65 + item.certainty * 0.35);
        }
        plan.confidence = clamp_double(std::max(best, plan.belief_score), 0.0, 1.0);
        const bool has_grounded_text = !plan.evidence.empty() && !plan.direct.empty();
        plan.verified = has_grounded_text && plan.confidence >= 0.42 && plan.belief_label != "unverified";
        if (!plan.verified && plan.caveats.empty()) {
            plan.caveats.push_back("Local memory mein abhi verified evidence weak hai.");
        }
        return plan.verified;
    }
};

class MythosCore {
public:
    static std::string identity_text(int sentence_count, std::size_t triple_count,
                                     bool offline_only, const std::string& mode) {
        std::ostringstream out;
        out << "INFINITY v5.5: living knowledge organism, strict verifier, non-LLM.\n"
            << "Main Claude/GPT nahi hoon, aur unka internal model copy nahi karta. "
            << "Mera mythos: local memory, symbolic reasoning, honest boundaries.\n"
            << "Verifier oath: bina evidence ke confident claim nahi.\n"
            << "Mode: " << mode << " | Offline answering: "
            << (offline_only ? "ON" : "OFF") << "\n"
            << "Memory: " << sentence_count << " sentences | "
            << triple_count << " triples\n";
        return out.str();
    }

    static std::string compose(const AnswerPlan& plan, const std::string& mode) {
        std::ostringstream out;
        if (!plan.verified) {
            out << "[INFINITY:v5.5] Strict verifier bol raha hai: is sawaal ka verified jawab "
                << "mere local memory mein abhi strong nahi hai.\n";
            if (!plan.skill.empty()) {
                out << "Skill route: " << plan.skill << " (" << SkillEngine::describe(plan.skill) << ")\n";
            }
            if (!plan.query.entities.empty()) {
                out << "Best learning target: " << plan.query.entities.front().text << "\n";
            }
            const std::string topic = plan.query.entities.empty() ? "" : plan.query.entities.front().text;
            out << KnowledgeGrowthEngine::gap_instruction(topic) << " Memory grow karo.\n";
            if (mode == "mythos") {
                out << "Mythos note: khaali jagah ko main claim nahi banata; use learning gap banata hoon.\n";
            }
            return out.str();
        }

        out << plan.direct << "\n";
        out << "[belief: " << plan.belief_label << " | skill: " << plan.skill << "]\n";
        if (!plan.bullets.empty()) {
            out << "\nKey verified points:\n";
            for (const std::string& bullet : plan.bullets) {
                out << "  - " << bullet << "\n";
            }
        }
        if ((mode == "reason" || mode == "mythos") && !plan.reasoning_steps.empty()) {
            out << "\nReasoning:\n";
            for (const std::string& step : plan.reasoning_steps) {
                out << "  - " << step << "\n";
            }
        }
        if (!plan.caveats.empty()) {
            out << "\nCaveat: " << plan.caveats.front() << "\n";
        }
        if (mode == "agent") {
            out << "\nNext action: `why` se evidence dekho, ya topic expand karne ke liye `deep <topic>`.\n";
        } else if (mode == "mythos") {
            out << "\n[Mythos] Memory ne jo pakka dekha, wahi bola. Baaki ko gap rakha.\n";
        }
        return out.str();
    }
};

struct WikiPage {
    std::string topic;
    std::string title;
    std::string summary;
    std::string url;
    std::vector<std::string> links;
    bool ok{false};
};

class HyperCrawler {
public:
    struct CrawlReport {
        std::vector<WikiPage> pages;
        int pages_fetched{0};
        int triples_added{0};
        double duration_seconds{0.0};
    };

    static WikiPage fetch_page(const std::string& topic) {
        WikiPage page;
        page.topic = topic;
        const std::string canonical = canonical_topic(topic);
        const std::string summary_url = "https://en.wikipedia.org/api/rest_v1/page/summary/" + url_encode(canonical);
        HttpResponse response = HttpClient::get(summary_url, 15);
        if (!response.ok || response.body.empty()) {
            return page;
        }
        page.title = extract_json_string(response.body, "title");
        page.summary = extract_json_string(response.body, "extract");
        page.url = "https://en.wikipedia.org/wiki/" + url_encode(page.title.empty() ? canonical : page.title);
        page.links = fetch_links(page.title.empty() ? canonical : page.title);
        page.ok = !page.title.empty() && !page.summary.empty();
        return page;
    }

    static CrawlReport crawl_topic(const std::string& root_topic, int max_threads, int depth = 1, int links_per_page = 10) {
        const auto start = std::chrono::steady_clock::now();
        CrawlReport report;

        std::vector<std::pair<std::string, int>> frontier{{root_topic, 0}};
        std::unordered_set<std::string> visited;
        visited.insert(lower_copy(root_topic));

        while (!frontier.empty()) {
            std::vector<std::pair<std::string, int>> current = frontier;
            frontier.clear();
            std::vector<WikiPage> fetched(current.size());
            std::atomic<int> index{0};
            const int thread_count = std::max(1, std::min(max_threads, static_cast<int>(current.size())));
            std::vector<std::thread> workers;
            workers.reserve(static_cast<std::size_t>(thread_count));

            for (int i = 0; i < thread_count; ++i) {
                workers.emplace_back([&]() {
                    while (true) {
                        const int slot = index.fetch_add(1);
                        if (slot >= static_cast<int>(current.size())) {
                            break;
                        }
                        fetched[static_cast<std::size_t>(slot)] = fetch_page(current[static_cast<std::size_t>(slot)].first);
                    }
                });
            }
            for (std::thread& worker : workers) {
                if (worker.joinable()) {
                    worker.join();
                }
            }

            for (std::size_t i = 0; i < current.size(); ++i) {
                const int current_depth = current[i].second;
                if (!fetched[i].ok) {
                    continue;
                }
                report.pages_fetched += 1;
                report.pages.push_back(fetched[i]);
                if (current_depth >= depth) {
                    continue;
                }
                int used = 0;
                for (const std::string& link : fetched[i].links) {
                    const std::string lowered = lower_copy(link);
                    if (visited.insert(lowered).second) {
                        frontier.emplace_back(link, current_depth + 1);
                        used += 1;
                        if (used >= links_per_page) {
                            break;
                        }
                    }
                }
            }
        }

        report.duration_seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        return report;
    }

private:
    static std::string canonical_topic(std::string topic) {
        topic = trim_copy(topic);
        if (topic.empty()) {
            return topic;
        }
        topic[0] = static_cast<char>(std::toupper(static_cast<unsigned char>(topic[0])));
        return topic;
    }

    static std::string url_encode(const std::string& input) {
        std::ostringstream oss;
        for (unsigned char c : input) {
            if (std::isalnum(c) || c == '-' || c == '_' || c == '.' || c == '~') {
                oss << static_cast<char>(c);
            } else if (c == ' ') {
                oss << '_';
            } else {
                oss << '%' << std::uppercase << std::hex << std::setw(2) << std::setfill('0')
                    << static_cast<int>(c) << std::nouppercase << std::dec;
            }
        }
        return oss.str();
    }

    static std::string extract_json_string(const std::string& json, const std::string& key) {
        const std::string needle = "\"" + key + "\":\"";
        std::size_t pos = json.find(needle);
        if (pos == std::string::npos) {
            return {};
        }
        pos += needle.size();
        std::string out;
        while (pos < json.size()) {
            const char c = json[pos++];
            if (c == '\\' && pos < json.size()) {
                const char escaped = json[pos++];
                switch (escaped) {
                    case 'n':
                        out.push_back('\n');
                        break;
                    case 't':
                        out.push_back('\t');
                        break;
                    case '"':
                    case '\\':
                    case '/':
                        out.push_back(escaped);
                        break;
                    default:
                        out.push_back(escaped);
                        break;
                }
                continue;
            }
            if (c == '"') {
                break;
            }
            out.push_back(c);
        }
        return out;
    }

    static std::vector<std::string> fetch_links(const std::string& topic) {
        const std::string url =
            "https://en.wikipedia.org/w/api.php?action=query&titles=" + url_encode(topic) +
            "&prop=links&pllimit=25&format=json";
        const HttpResponse response = HttpClient::get(url, 15);
        if (!response.ok || response.body.empty()) {
            return {};
        }

        std::vector<std::string> links;
        std::size_t pos = 0;
        while ((pos = response.body.find("\"title\":\"", pos)) != std::string::npos) {
            pos += 9;
            std::string title;
            while (pos < response.body.size()) {
                const char c = response.body[pos++];
                if (c == '\\' && pos < response.body.size()) {
                    title.push_back(response.body[pos++]);
                    continue;
                }
                if (c == '"') {
                    break;
                }
                title.push_back(c);
            }
            if (!title.empty() && title != topic) {
                links.push_back(title);
            }
        }
        std::sort(links.begin(), links.end());
        links.erase(std::unique(links.begin(), links.end()), links.end());
        return links;
    }
};

struct ContradictionRecord {
    int64_t left_id{0};
    int64_t right_id{0};
    std::string left_fact;
    std::string right_fact;
    std::string reason;
};

class ContradictionDetector {
public:
    std::vector<ContradictionRecord> scan(const KnowledgeMesh& mesh, int64_t min_recent_timestamp = 0) const {
        std::vector<TripleRecord> triples = mesh.snapshot();
        std::vector<ContradictionRecord> out;
        std::unordered_map<std::string, std::vector<TripleRecord>> grouped;
        for (const TripleRecord& triple : triples) {
            if (min_recent_timestamp > 0 && triple.last_seen < min_recent_timestamp) {
                continue;
            }
            grouped[triple.subject + "\x1f" + triple.relation].push_back(triple);
        }

        for (auto& bucket : grouped) {
            auto& records = bucket.second;
            for (std::size_t i = 0; i < records.size(); ++i) {
                for (std::size_t j = i + 1; j < records.size(); ++j) {
                    if (records[i].object != records[j].object) {
                        out.push_back({
                            records[i].id,
                            records[j].id,
                            records[i].subject + " --[" + records[i].relation + "]--> " + records[i].object,
                            records[j].subject + " --[" + records[j].relation + "]--> " + records[j].object,
                            "same subject and relation, different objects"
                        });
                    }
                }
            }
        }

        static const std::vector<std::pair<std::string, std::string>> opposite_relations = {
            {"CAUSES", "PREVENTS"},
            {"ENABLES", "PREVENTS"},
            {"SUPPORTS", "REFUTES"}
        };

        for (const auto& pair : opposite_relations) {
            for (const TripleRecord& a : triples) {
                if (upper_copy(a.relation) != pair.first) {
                    continue;
                }
                for (const TripleRecord& b : triples) {
                    if (a.id == b.id) {
                        continue;
                    }
                    if (a.subject == b.subject && a.object == b.object && upper_copy(b.relation) == pair.second) {
                        out.push_back({
                            a.id,
                            b.id,
                            a.subject + " --[" + a.relation + "]--> " + a.object,
                            b.subject + " --[" + b.relation + "]--> " + b.object,
                            "opposite semantic relations"
                        });
                    }
                }
            }
        }

        return out;
    }
};

struct VerificationResult {
    bool is_valid{false};
    double confidence{0.0};
    std::string reason;
    std::vector<int64_t> support_ids;
    std::vector<int64_t> contradiction_ids;
};

class FactVerifier {
public:
    FactVerifier(const KnowledgeMesh& mesh, const ContradictionDetector& contradictions)
        : mesh_(mesh), contradictions_(contradictions) {}

    VerificationResult verify(const std::string& subject,
                              const std::string& relation,
                              const std::string& object,
                              TemporalState temporal = TemporalState::Present) const {
        VerificationResult result;
        const std::string subject_lower = lower_copy(subject);
        const std::string relation_lower = lower_copy(relation);
        const std::string object_lower = lower_copy(object);
        const auto exact = mesh_.get_exact(subject, relation, object);
        if (exact.has_value()) {
            result.is_valid = true;
            result.confidence = clamp_double(static_cast<double>(exact->certainty) *
                                             clamp_double(static_cast<double>(exact->weight), 0.0, 1.0),
                                             0.0, 1.0);
            result.reason = "exact triple present in mesh";
            result.support_ids.push_back(exact->id);
            if (exact->contradiction_flag) {
                result.confidence *= 0.6;
                result.reason += " (contradiction penalty)";
            }
            if (temporal == TemporalState::Present && exact->temporal == TemporalState::Past) {
                result.confidence *= 0.7;
                result.reason += " (temporal penalty)";
            }
            return result;
        }

        static const std::vector<std::pair<std::string, std::string>> opposite_relations = {
            {"causes", "prevents"},
            {"enables", "prevents"},
            {"supports", "refutes"}
        };

        for (const TripleRecord& triple : mesh_.outgoing(subject)) {
            const std::string triple_relation = lower_copy(triple.relation);
            const std::string triple_object = lower_copy(triple.object);
            if (triple_relation == relation_lower && triple_object != object_lower) {
                result.is_valid = false;
                result.confidence = 0.0;
                result.reason = "same subject and relation point to a different object";
                result.contradiction_ids.push_back(triple.id);
                return result;
            }
            for (const auto& pair : opposite_relations) {
                const bool direct = relation_lower == pair.first && triple_relation == pair.second;
                const bool inverse = relation_lower == pair.second && triple_relation == pair.first;
                if ((direct || inverse) && triple_object == object_lower) {
                    result.is_valid = false;
                    result.confidence = 0.0;
                    result.reason = "opposite semantic relation already present";
                    result.contradiction_ids.push_back(triple.id);
                    return result;
                }
            }
        }

        const auto contradictions = contradictions_.scan(mesh_);
        for (const auto& contradiction : contradictions) {
            const std::string left = lower_copy(contradiction.left_fact);
            const std::string right = lower_copy(contradiction.right_fact);
            const bool mentions_fact =
                (left.find(subject_lower) != std::string::npos &&
                 left.find(relation_lower) != std::string::npos &&
                 left.find(object_lower) != std::string::npos) ||
                (right.find(subject_lower) != std::string::npos &&
                 right.find(relation_lower) != std::string::npos &&
                 right.find(object_lower) != std::string::npos);
            if (mentions_fact) {
                result.is_valid = false;
                result.confidence = 0.0;
                result.reason = contradiction.reason;
                result.contradiction_ids = {contradiction.left_id, contradiction.right_id};
                return result;
            }
        }

        result.is_valid = true;
        result.confidence = 0.3;
        result.reason = "unknown triple, no internal contradiction";
        return result;
    }

private:
    const KnowledgeMesh& mesh_;
    const ContradictionDetector& contradictions_;
};

enum class Valence {
    Harmonious,
    Neutral,
    Dissonant
};

struct AgentReport {
    std::string agent;
    std::string action;
    std::string detail;
    std::size_t triples_contributed{0};
    std::size_t contradictions_found{0};
    double reward{0.0};
    int64_t at{0};
};

class SharedMemory {
public:
    void publish_fact(int64_t triple_id) {
        std::lock_guard<std::mutex> lock(mutex_);
        new_triple_ids_.push_back(triple_id);
    }

    std::vector<int64_t> drain_new_facts(std::size_t limit = 2048) {
        std::lock_guard<std::mutex> lock(mutex_);
        const std::size_t take = std::min(limit, new_triple_ids_.size());
        std::vector<int64_t> out;
        out.reserve(take);
        for (std::size_t i = 0; i < take; ++i) {
            out.push_back(new_triple_ids_.front());
            new_triple_ids_.pop_front();
        }
        return out;
    }

    void publish_report(const AgentReport& report) {
        std::lock_guard<std::mutex> lock(mutex_);
        reports_[report.agent] = report;
    }

    std::vector<AgentReport> reports() const {
        std::lock_guard<std::mutex> lock(mutex_);
        std::vector<AgentReport> out;
        out.reserve(reports_.size());
        for (const auto& entry : reports_) {
            out.push_back(entry.second);
        }
        std::sort(out.begin(), out.end(), [](const AgentReport& a, const AgentReport& b) {
            return a.agent < b.agent;
        });
        return out;
    }

private:
    mutable std::mutex mutex_;
    std::deque<int64_t> new_triple_ids_;
    std::unordered_map<std::string, AgentReport> reports_;
};

class ActionValueEstimator {
public:
    explicit ActionValueEstimator(std::string path)
        : path_(std::move(path)) {
        load();
    }

    ~ActionValueEstimator() {
        save();
    }

    std::pair<std::string, bool> choose(const std::string& category,
                                        const std::vector<std::string>& actions,
                                        std::mt19937_64& rng) const {
        if (actions.empty()) {
            return {"", false};
        }
        std::uniform_real_distribution<double> prob(0.0, 1.0);
        if (actions.size() == 1 || prob(rng) < EPSILON_GREEDY) {
            std::uniform_int_distribution<std::size_t> pick(0, actions.size() - 1);
            return {actions[pick(rng)], true};
        }

        std::lock_guard<std::mutex> lock(mutex_);
        double best_value = -std::numeric_limits<double>::infinity();
        std::string best = actions.front();
        for (const std::string& action : actions) {
            const double value = value_unlocked(category, action);
            if (value > best_value) {
                best_value = value;
                best = action;
            }
        }
        return {best, false};
    }

    void update(const std::string& category, const std::string& action, double reward) {
        std::lock_guard<std::mutex> lock(mutex_);
        const std::string key = make_key(category, action);
        double& q_value = table_[key];
        q_value = q_value + 0.15 * (reward - q_value);
        dirty_ = true;
    }

    double value(const std::string& category, const std::string& action) const {
        std::lock_guard<std::mutex> lock(mutex_);
        return value_unlocked(category, action);
    }

    void save() const {
        std::lock_guard<std::mutex> lock(mutex_);
        if (!dirty_) {
            return;
        }
        std::ofstream out(path_, std::ios::binary | std::ios::trunc);
        if (!out) {
            Logger::console("QTABLE", "Failed to save " + path_, COLOR_RED);
            return;
        }
        const uint64_t count = table_.size();
        out.write(reinterpret_cast<const char*>(&count), sizeof(count));
        for (const auto& entry : table_) {
            const uint64_t length = entry.first.size();
            out.write(reinterpret_cast<const char*>(&length), sizeof(length));
            out.write(entry.first.data(), static_cast<std::streamsize>(length));
            out.write(reinterpret_cast<const char*>(&entry.second), sizeof(entry.second));
        }
        dirty_ = false;
    }

private:
    static std::string make_key(const std::string& category, const std::string& action) {
        return category + "|" + action;
    }

    double value_unlocked(const std::string& category, const std::string& action) const {
        const auto it = table_.find(make_key(category, action));
        return it == table_.end() ? 0.0 : it->second;
    }

    void load() {
        std::lock_guard<std::mutex> lock(mutex_);
        std::ifstream in(path_, std::ios::binary);
        if (!in) {
            return;
        }
        uint64_t count = 0;
        in.read(reinterpret_cast<char*>(&count), sizeof(count));
        for (uint64_t i = 0; i < count && in.good(); ++i) {
            uint64_t length = 0;
            in.read(reinterpret_cast<char*>(&length), sizeof(length));
            std::string key(length, '\0');
            in.read(key.data(), static_cast<std::streamsize>(length));
            double value = 0.0;
            in.read(reinterpret_cast<char*>(&value), sizeof(value));
            table_[key] = value;
        }
        dirty_ = false;
    }

    std::string path_;
    mutable std::mutex mutex_;
    mutable bool dirty_{false};
    std::unordered_map<std::string, double> table_;
};

struct ReasoningHop {
    std::string subject;
    std::string relation;
    std::string object;
    double confidence{0.0};
};

class ReasoningCortex {
public:
    explicit ReasoningCortex(KnowledgeMesh& mesh)
        : mesh_(mesh) {}

    std::vector<ReasoningHop> transitive_infer(std::size_t limit = 32) const {
        const std::vector<TripleRecord> snapshot = mesh_.snapshot();
        std::unordered_map<std::string, std::vector<TripleRecord>> adj;
        for (const TripleRecord& triple : snapshot) {
            adj[triple.subject].push_back(triple);
        }

        std::vector<ReasoningHop> out;
        for (const auto& entry : adj) {
            for (const TripleRecord& left : entry.second) {
                auto mid_it = adj.find(left.object);
                if (mid_it == adj.end()) {
                    continue;
                }
                for (const TripleRecord& right : mid_it->second) {
                    if (left.subject == right.object) {
                        continue;
                    }
                    const double confidence =
                        static_cast<double>(left.certainty * left.weight) *
                        static_cast<double>(right.certainty * right.weight) / 25.0;
                    out.push_back({left.subject, left.relation + "_THEN_" + right.relation, right.object, confidence});
                    if (out.size() >= limit) {
                        return out;
                    }
                }
            }
        }
        return out;
    }

    std::vector<std::vector<ReasoningHop>> deduce(const std::string& subject,
                                                  const std::string& relation,
                                                  int max_depth = 4) const {
        std::vector<std::vector<ReasoningHop>> out;
        std::vector<ReasoningHop> path;
        dfs(subject, relation, max_depth, path, out);
        return out;
    }

private:
    void dfs(const std::string& current,
             const std::string& relation,
             int depth,
             std::vector<ReasoningHop>& path,
             std::vector<std::vector<ReasoningHop>>& out) const {
        if (depth <= 0) {
            return;
        }
        const std::vector<TripleRecord> outgoing = mesh_.outgoing(current);
        for (const TripleRecord& triple : outgoing) {
            if (!relation.empty() && lower_copy(triple.relation) != lower_copy(relation)) {
                continue;
            }
            path.push_back({triple.subject, triple.relation, triple.object,
                            static_cast<double>(triple.certainty * triple.weight) / 5.0});
            out.push_back(path);
            dfs(triple.object, relation, depth - 1, path, out);
            path.pop_back();
        }
    }

    KnowledgeMesh& mesh_;
};

struct HopPath {
    std::vector<ReasoningHop> steps;
    double confidence{0.0};
};

class MultiHopReasoner {
public:
    explicit MultiHopReasoner(const KnowledgeMesh& mesh)
        : mesh_(mesh) {}

    std::optional<HopPath> find(const std::string& start, const std::string& target, int max_depth = 5) const {
        const std::string target_lower = lower_copy(target);
        struct Node {
            std::string node_name;
            std::vector<ReasoningHop> path;
            double confidence;
            Node(std::string n, std::vector<ReasoningHop> p, double c)
                : node_name(std::move(n)), path(std::move(p)), confidence(c) {}
        };

        std::queue<Node> queue;
        queue.push(Node{start, {}, 1.0});
        std::unordered_set<std::string> visited{lower_copy(start)};

        while (!queue.empty()) {
            Node node = queue.front();
            queue.pop();
            if (static_cast<int>(node.path.size()) >= max_depth) {
                continue;
            }
            for (const TripleRecord& triple : mesh_.outgoing(node.node_name)) {
                const std::string next_lower = lower_copy(triple.object);
                if (!visited.insert(next_lower).second) {
                    continue;
                }
                Node next = node;
                next.path.push_back({triple.subject, triple.relation, triple.object,
                                     static_cast<double>(triple.certainty * triple.weight) / 5.0});
                next.confidence *= std::max(0.01, next.path.back().confidence);
                if (next_lower == target_lower) {
                    return HopPath{next.path, next.confidence};
                }
                queue.push(std::move(next));
            }
        }
        return std::nullopt;
    }

private:
    const KnowledgeMesh& mesh_;
};

struct Vitals {
    double cpu_percent{0.0};
    double ram_free_ratio{1.0};
    int thread_count{1};
    uintmax_t db_size_bytes{0};
    bool network_available{false};
    double load_average{0.0};
};

struct AutonomicState {
    bool slow_mode{false};
    bool pause_learning{false};
    int crawler_threads{DEFAULT_CRAWLER_THREADS};
    double last_tick_ms{0.0};
    Vitals last_vitals;
};

class Medulla {
public:
    explicit Medulla(std::string db_path)
        : db_path_(std::move(db_path)) {}

    Vitals pulse() {
        Vitals vitals;
        vitals.cpu_percent = read_cpu_percent();
        vitals.ram_free_ratio = read_ram_free_ratio();
        vitals.thread_count = read_self_thread_count();
        vitals.db_size_bytes = read_db_size();
        vitals.network_available = HttpClient::get("https://en.wikipedia.org/wiki/Main_Page", 5, true).ok;
        vitals.load_average = read_load_average();

        Logger::append_file("organism_vitals.log",
            now_string() + " cpu=" + format_double(vitals.cpu_percent, 2) +
            " ram_free=" + format_double(vitals.ram_free_ratio, 3) +
            " threads=" + std::to_string(vitals.thread_count) +
            " db_bytes=" + std::to_string(vitals.db_size_bytes) +
            " network=" + std::string(vitals.network_available ? "up" : "down") +
            " load=" + format_double(vitals.load_average, 2));
        return vitals;
    }

    void handle_reflex(const Vitals& vitals, AutonomicState& state) const {
        state.last_vitals = vitals;
        state.pause_learning = vitals.ram_free_ratio < 0.10;
        state.slow_mode = vitals.cpu_percent > 85.0 || state.last_tick_ms > 10000.0;
        state.crawler_threads = state.slow_mode ? SLOW_CRAWLER_THREADS : DEFAULT_CRAWLER_THREADS;
    }

private:
    double read_cpu_percent() {
        std::ifstream in("/proc/stat");
        std::string label;
        uint64_t user = 0;
        uint64_t nice = 0;
        uint64_t system = 0;
        uint64_t idle = 0;
        uint64_t iowait = 0;
        uint64_t irq = 0;
        uint64_t softirq = 0;
        uint64_t steal = 0;
        in >> label >> user >> nice >> system >> idle >> iowait >> irq >> softirq >> steal;
        const uint64_t idle_all = idle + iowait;
        const uint64_t total = user + nice + system + idle + iowait + irq + softirq + steal;
        const uint64_t idle_delta = last_idle_ == 0 ? 0 : idle_all - last_idle_;
        const uint64_t total_delta = last_total_ == 0 ? 0 : total - last_total_;
        last_idle_ = idle_all;
        last_total_ = total;
        if (total_delta == 0) {
            return 0.0;
        }
        return 100.0 * (1.0 - static_cast<double>(idle_delta) / static_cast<double>(total_delta));
    }

    double read_ram_free_ratio() const {
        std::ifstream in("/proc/meminfo");
        std::string key;
        uint64_t value = 0;
        std::string unit;
        double total = 0.0;
        double available = 0.0;
        while (in >> key >> value >> unit) {
            if (key == "MemTotal:") {
                total = static_cast<double>(value);
            } else if (key == "MemAvailable:") {
                available = static_cast<double>(value);
            }
        }
        if (total <= 0.0) {
            return 1.0;
        }
        return available / total;
    }

    int read_self_thread_count() const {
        std::ifstream in("/proc/self/status");
        std::string line;
        while (std::getline(in, line)) {
            if (line.rfind("Threads:", 0) == 0) {
                return std::stoi(trim_copy(line.substr(8)));
            }
        }
        return 1;
    }

    uintmax_t read_db_size() const {
        std::error_code ec;
        if (!fs::exists(db_path_, ec)) {
            return 0;
        }
        const uintmax_t size = fs::file_size(db_path_, ec);
        return ec ? 0 : size;
    }

    static double read_load_average() {
        std::ifstream in("/proc/loadavg");
        double load = 0.0;
        in >> load;
        return load;
    }

    std::string db_path_;
    uint64_t last_idle_{0};
    uint64_t last_total_{0};
};

struct HungerState {
    double curiosity_hunger{0.0};
    double mesh_entropy{0.0};
    double sparse_ratio{0.0};
    double unresolved_ratio{0.0};
    std::vector<std::pair<std::string, float>> top_hungry;
};

class Hypothalamus {
public:
    HungerState compute(const KnowledgeMesh& mesh, const OmegaMemory& omega) const {
        HungerState state;
        state.mesh_entropy = mesh.global_entropy();
        state.sparse_ratio = mesh.sparse_ratio();
        const int total_queries = std::max(1, omega.total_query_count());
        state.unresolved_ratio = static_cast<double>(omega.unresolved_query_count()) / static_cast<double>(total_queries);
        state.top_hungry = mesh.entropy_ranking(5);

        const double entropy_component = clamp_double(state.mesh_entropy / 4.0, 0.0, 1.0);
        state.curiosity_hunger = clamp_double(
            0.5 * entropy_component +
            0.3 * state.sparse_ratio +
            0.2 * state.unresolved_ratio,
            0.0, 1.0);
        return state;
    }
};

class LimbicSystem {
public:
    Valence evaluate(const TripleRecord& triple, const KnowledgeMesh& mesh) const {
        const std::size_t corroboration = mesh.corroboration_count(triple.id);
        if (triple.contradiction_flag || triple.certainty < 0.4f) {
            return Valence::Dissonant;
        }
        if (triple.certainty > 0.85f && corroboration >= 2 && !triple.contradiction_flag) {
            return Valence::Harmonious;
        }
        return Valence::Neutral;
    }

    void consolidate(KnowledgeMesh& mesh,
                     const std::vector<int64_t>& ids,
                     const std::function<void(int64_t)>& persist_one) const {
        for (int64_t id : ids) {
            const auto record = mesh.get_by_id(id);
            if (!record.has_value()) {
                continue;
            }
            const Valence valence = evaluate(*record, mesh);
            if (valence == Valence::Harmonious) {
                mesh.adjust_weight(id, 0.08f);
                mesh.scale_certainty(id, 1.02f);
                persist_one(id);
            } else if (valence == Valence::Dissonant) {
                mesh.adjust_weight(id, -0.10f);
                mesh.scale_certainty(id, 0.80f);
                mesh.set_quarantined(id, true);
                persist_one(id);
                Logger::append_file(
                    "dissonant_facts.log",
                    now_string() + " id=" + std::to_string(id) + " fact=" +
                    record->subject + " --[" + record->relation + "]--> " + record->object +
                    " certainty=" + format_double(record->certainty, 3));
            }
        }
    }
};

enum class ActionKind {
    CrawlTopic,
    ConsolidateMemory,
    VerifyHypothesis,
    ContradictionSweep,
    SaveState
};

std::string action_name(ActionKind kind) {
    switch (kind) {
        case ActionKind::CrawlTopic:
            return "CRAWL_TOPIC";
        case ActionKind::ConsolidateMemory:
            return "CONSOLIDATE_MEMORY";
        case ActionKind::VerifyHypothesis:
            return "VERIFY_HYPOTHESIS";
        case ActionKind::ContradictionSweep:
            return "CONTRADICTION_SWEEP";
        case ActionKind::SaveState:
            return "SAVE_STATE";
    }
    return "UNKNOWN";
}

struct PlannedAction {
    ActionKind kind{ActionKind::SaveState};
    std::string target;
    double cost{0.0};
    std::string description;
};

struct GoalDescription {
    std::string raw;
    std::string kind;
    std::string target;
};

struct PlanningState {
    bool network_available{true};
    bool pause_learning{false};
    bool dirty_state{false};
    bool has_candidate_hypothesis{false};
    bool contradiction_backlog{false};
    double cpu_percent{0.0};
    double hunger{0.0};
};

class WorldPlanner {
public:
    std::vector<PlannedAction> plan(const GoalDescription& goal, const PlanningState& state) const {
        const unsigned target_mask = required_mask(goal, state);
        struct Node {
            unsigned mask;
            double cost;
            std::vector<PlannedAction> path;
        };
        auto heuristic = [&](unsigned mask) {
            unsigned missing = target_mask & (~mask);
            double h = 0.0;
            while (missing != 0U) {
                h += 0.75;
                missing &= (missing - 1U);
            }
            return h;
        };
        auto cmp = [&](const Node& a, const Node& b) {
            return (a.cost + heuristic(a.mask)) > (b.cost + heuristic(b.mask));
        };
        std::priority_queue<Node, std::vector<Node>, decltype(cmp)> open(cmp);
        open.push({0U, 0.0, {}});
        std::unordered_map<unsigned, double> best_cost;
        best_cost[0U] = 0.0;

        while (!open.empty()) {
            Node current = open.top();
            open.pop();
            if ((current.mask & target_mask) == target_mask) {
                return current.path;
            }
            for (const PlannedAction& action : available_actions(goal, state)) {
                const unsigned next_mask = current.mask | bit_for(action.kind);
                const double next_cost = current.cost + action.cost;
                auto it = best_cost.find(next_mask);
                if (it != best_cost.end() && it->second <= next_cost) {
                    continue;
                }
                best_cost[next_mask] = next_cost;
                Node next = current;
                next.mask = next_mask;
                next.cost = next_cost;
                next.path.push_back(action);
                open.push(std::move(next));
            }
        }
        return {};
    }

private:
    static unsigned bit_for(ActionKind kind) {
        switch (kind) {
            case ActionKind::CrawlTopic:
                return 1u << 0;
            case ActionKind::ConsolidateMemory:
                return 1u << 1;
            case ActionKind::VerifyHypothesis:
                return 1u << 2;
            case ActionKind::ContradictionSweep:
                return 1u << 3;
            case ActionKind::SaveState:
                return 1u << 4;
        }
        return 0U;
    }

    static unsigned required_mask(const GoalDescription& goal, const PlanningState& state) {
        unsigned mask = 0U;
        if (goal.kind == "learn") {
            mask |= bit_for(ActionKind::CrawlTopic);
            mask |= bit_for(ActionKind::SaveState);
            if (state.contradiction_backlog) {
                mask |= bit_for(ActionKind::ContradictionSweep);
            }
        } else if (goal.kind == "verify") {
            mask |= bit_for(ActionKind::VerifyHypothesis);
            mask |= bit_for(ActionKind::SaveState);
        } else if (goal.kind == "stabilize") {
            mask |= bit_for(ActionKind::ConsolidateMemory);
            mask |= bit_for(ActionKind::ContradictionSweep);
            mask |= bit_for(ActionKind::SaveState);
        } else {
            mask |= bit_for(ActionKind::SaveState);
        }
        return mask;
    }

    static std::vector<PlannedAction> available_actions(const GoalDescription& goal, const PlanningState& state) {
        std::vector<PlannedAction> out;
        if (!goal.target.empty() && state.network_available && !state.pause_learning) {
            out.push_back({ActionKind::CrawlTopic, goal.target,
                           1.0 + state.cpu_percent / 100.0 + state.hunger,
                           "crawl " + goal.target});
        }
        if (state.has_candidate_hypothesis) {
            out.push_back({ActionKind::VerifyHypothesis, "", 0.9 + state.hunger * 0.2, "verify oldest candidate"});
        }
        if (state.contradiction_backlog) {
            out.push_back({ActionKind::ContradictionSweep, "", 0.8 + state.cpu_percent / 200.0, "sweep contradictions"});
        }
        if (state.dirty_state || state.pause_learning) {
            out.push_back({ActionKind::ConsolidateMemory, "", 0.7, "consolidate memory"});
        }
        out.push_back({ActionKind::SaveState, "", 0.5, "persist state"});
        return out;
    }
};

struct FrontalDecision {
    std::string primary_concept;
    std::vector<std::string> candidate_topics;
    std::vector<PlannedAction> plan;
};

class FrontalCortex {
public:
    FrontalDecision analyze(const PlanningState& state,
                            const HungerState& hunger,
                            const KnowledgeMesh& mesh,
                            const OmegaMemory& omega,
                            const WorldPlanner& planner) const {
        FrontalDecision decision;
        if (!hunger.top_hungry.empty()) {
            decision.primary_concept = hunger.top_hungry.front().first;
        } else {
            decision.primary_concept = "knowledge";
        }

        decision.candidate_topics.push_back(decision.primary_concept);
        for (const std::string& related : omega.related_topics(decision.primary_concept, 5)) {
            decision.candidate_topics.push_back(related);
        }
        for (const auto& nearby : mesh.nearest_concepts(decision.primary_concept, 5)) {
            decision.candidate_topics.push_back(nearby.first);
        }
        std::sort(decision.candidate_topics.begin(), decision.candidate_topics.end());
        decision.candidate_topics.erase(
            std::unique(decision.candidate_topics.begin(), decision.candidate_topics.end()),
            decision.candidate_topics.end());

        const GoalDescription goal{"learn " + decision.primary_concept, "learn", decision.primary_concept};
        decision.plan = planner.plan(goal, state);
        return decision;
    }
};

struct GeneratedHypothesis {
    HypothesisRecord record;
    std::string classification;
};

class HypothesisGenerator {
public:
    HypothesisGenerator(KnowledgeMesh& mesh,
                        HypothesisStore& hypotheses,
                        ParadoxStore& paradoxes)
        : mesh_(mesh), hypotheses_(hypotheses), paradoxes_(paradoxes) {}

    std::vector<GeneratedHypothesis> generate(std::size_t limit) {
        const auto entropy = mesh_.entropy_ranking(12);
        std::vector<GeneratedHypothesis> out;
        for (std::size_t i = 0; i < entropy.size() && out.size() < limit; ++i) {
            for (std::size_t j = i + 1; j < entropy.size() && out.size() < limit; ++j) {
                const std::string& a = entropy[i].first;
                const std::string& b = entropy[j].first;
                if (a == b || already_connected(a, b)) {
                    continue;
                }
                const float sim = mesh_.concept_similarity(a, b);
                if (sim < 0.08f || sim > 0.90f) {
                    continue;
                }
                HypothesisRecord record;
                record.subject = a;
                record.object = b;
                record.relation = mesh_.dominant_relation(a);
                record.confidence = clamp_double(
                    0.35 + 0.30 * sim +
                    0.20 * (entropy[i].second / (1.0 + entropy[i].second)) +
                    0.15 * (entropy[j].second / (1.0 + entropy[j].second)),
                    0.0, 1.0);
                record.status = "CANDIDATE";
                record.trigger_concept = entropy[i].second >= entropy[j].second ? a : b;
                record.generated_at = now_epoch();

                if (contradicts_existing(record)) {
                    paradoxes_.insert(record.subject, record.relation, record.object,
                                      record.confidence, "conflicts with existing edge");
                    out.push_back({record, "PARADOX"});
                    continue;
                }

                hypotheses_.upsert_candidate(record);
                out.push_back({record, "VALID"});
            }
        }
        return out;
    }

private:
    bool already_connected(const std::string& a, const std::string& b) const {
        const auto outgoing = mesh_.outgoing(a);
        for (const TripleRecord& triple : outgoing) {
            if (lower_copy(triple.object) == lower_copy(b)) {
                return true;
            }
        }
        return false;
    }

    bool contradicts_existing(const HypothesisRecord& record) const {
        const auto outgoing = mesh_.outgoing(record.subject);
        for (const TripleRecord& triple : outgoing) {
            if (lower_copy(triple.relation) == lower_copy(record.relation) &&
                lower_copy(triple.object) != lower_copy(record.object)) {
                return true;
            }
        }
        return false;
    }

    KnowledgeMesh& mesh_;
    HypothesisStore& hypotheses_;
    ParadoxStore& paradoxes_;
};

std::string derive_category(const std::string& topic, const std::string& summary) {
    const std::string haystack = lower_copy(topic + " " + summary);
    if (haystack.find("quantum") != std::string::npos || haystack.find("physics") != std::string::npos ||
        haystack.find("particle") != std::string::npos || haystack.find("relativity") != std::string::npos) {
        return "physics";
    }
    if (haystack.find("biology") != std::string::npos || haystack.find("cell") != std::string::npos ||
        haystack.find("genetic") != std::string::npos) {
        return "biology";
    }
    if (haystack.find("chemistry") != std::string::npos || haystack.find("molecule") != std::string::npos) {
        return "chemistry";
    }
    if (haystack.find("mathemat") != std::string::npos || haystack.find("equation") != std::string::npos) {
        return "mathematics";
    }
    if (haystack.find("computer") != std::string::npos || haystack.find("algorithm") != std::string::npos ||
        haystack.find("software") != std::string::npos) {
        return "computer_science";
    }
    if (haystack.find("history") != std::string::npos || haystack.find("empire") != std::string::npos ||
        haystack.find("war") != std::string::npos) {
        return "history";
    }
    return "general";
}

struct ActionOutcome {
    bool ok{false};
    std::string action;
    std::string message;
    double reward{0.0};
    int pages_fetched{0};
    int triples_added{0};
    int contradictions_found{0};
    std::vector<GeneratedHypothesis> hypotheses;
};

class SovereignBrain {
public:
    explicit SovereignBrain(const std::string& passphrase)
        : receptor_(passphrase),
          encoder_(),
          mesh_(encoder_),
          omega_("omega_memory.db"),
          hypotheses_("hypotheses.db"),
          paradoxes_("paradoxes.db"),
          q_table_("q_table.dat"),
          verifier_(mesh_, contradiction_detector_),
          cortex_(mesh_),
          hop_reasoner_(mesh_),
          medulla_(omega_.path()),
          hypothesis_generator_(mesh_, hypotheses_, paradoxes_) {
        const CURLcode curl_rc = curl_global_init(CURL_GLOBAL_ALL);
        if (curl_rc != CURLE_OK) {
            throw std::runtime_error(std::string("curl_global_init failed: ") + curl_easy_strerror(curl_rc));
        }
        try {
            omega_.load_mesh(mesh_);
            autonomic_.last_vitals.network_available = true;
            autonomic_.last_vitals.ram_free_ratio = 1.0;
            last_hunger_ = hypothalamus_.compute(mesh_, omega_);
            seed_topics_if_needed();
        } catch (...) {
            curl_global_cleanup();
            throw;
        }
    }

    ~SovereignBrain() {
        stop();
        curl_global_cleanup();
    }

    void start() {
        bool expected = false;
        if (!running_.compare_exchange_strong(expected, true)) {
            return;
        }

        {
            std::lock_guard<std::mutex> lock(state_mutex_);
            autonomic_.last_vitals = medulla_.pulse();
            medulla_.handle_reflex(autonomic_.last_vitals, autonomic_);
            last_hunger_ = hypothalamus_.compute(mesh_, omega_);
        }

        consciousness_thread_ = std::thread([this]() { resilient_loop("CONSCIOUSNESS", [this]() { consciousness_loop(); }); });
        explorer_thread_ = std::thread([this]() { resilient_loop("EXPLORER", [this]() { explorer_loop(); }); });
        optimizer_thread_ = std::thread([this]() { resilient_loop("OPTIMIZER", [this]() { optimizer_loop(); }); });
        safety_thread_ = std::thread([this]() { resilient_loop("SAFETY", [this]() { safety_loop(); }); });

        Logger::console("BOOT", "INFINITY organism online", COLOR_GREEN);
    }

    void stop() {
        bool expected = true;
        if (!running_.compare_exchange_strong(expected, false)) {
            return;
        }
        g_shutdown_requested.store(true);
        queue_cv_.notify_all();
        if (consciousness_thread_.joinable()) {
            consciousness_thread_.join();
        }
        if (explorer_thread_.joinable()) {
            explorer_thread_.join();
        }
        if (optimizer_thread_.joinable()) {
            optimizer_thread_.join();
        }
        if (safety_thread_.joinable()) {
            safety_thread_.join();
        }
        q_table_.save();
        save_snapshot("infinity_state.snapshot");
        Logger::console("SHUTDOWN", "Organism state persisted", COLOR_YELLOW);
    }

    std::string answer_question(const std::string& raw_question) {
        return answer_question_v55(raw_question);

        std::ostringstream out;

        // ── Step 1: classify intent ───────────────────────────────────
        const Intent intent = classify_intent(raw_question);

        if (intent == Intent::GREETING) {
            const std::string greeting_reply =
                "Namaste! Koi bhi topic seekhne ke liye 'learn <topic>' ya "
                "'deep <topic>' use karo. Sawaal poochne ke liye seedha type karo.";
            // update context but no entity
            if (context_window_.size() >= CTX_MAX) context_window_.pop_front();
            context_window_.push_back({raw_question, {}});
            return greeting_reply;
        }

        if (intent == Intent::SELF_QUERY) {
            const std::string self_reply =
                "Main INFINITY hoon — ek autonomous knowledge organism.\n"
                "Main Wikipedia se facts seekhta hoon, unhe semantic memory mein store karta hoon,\n"
                "aur reasoning chains ke zariye jawab deta hoon.\n"
                "Main opinions nahi rakhta. Main sirf verified facts present karta hoon.";
            if (context_window_.size() >= CTX_MAX) context_window_.pop_front();
            context_window_.push_back({raw_question, {}});
            return self_reply;
        }

        if (intent == Intent::OPINION) {
            // Surface relevant facts — no judgment
            const std::string resolved = resolve_pronouns(raw_question);
            const std::vector<Entity> ents = NEREngine::extract(resolved);
            std::string subject_hint;
            if (!ents.empty()) subject_hint = ents.front().text;
            else if (!context_window_.empty()) subject_hint = context_window_.back().last_entity;

            out << "[INFINITY] Yeh ek opinion-based sawaal hai. "
                   "Main nishpaksh hoon — koi judgment nahi deta.\n";
            if (!subject_hint.empty()) {
                out << "'" << subject_hint << "' ke baare mein jo facts mere paas hain:\n\n";
                auto search_hits = omega_.search(subject_hint);
                int shown = 0;
                for (const auto& hit : search_hits) {
                    if (lower_copy(hit.topic).find(lower_copy(subject_hint)) != std::string::npos ||
                        lower_copy(hit.text).find(lower_copy(subject_hint)) != std::string::npos) {
                        out << "  - " << trim_copy(hit.text) << "\n";
                        if (++shown >= 4) break;
                    }
                }
                if (shown == 0) {
                    out << "  (Abhi mere paas is topic ke facts nahi hain. "
                           "'learn " << subject_hint << "' try karo.)\n";
                }
            }
            if (context_window_.size() >= CTX_MAX) context_window_.pop_front();
            context_window_.push_back({raw_question, subject_hint});
            return out.str();
        }

        // ── Step 2: FACTUAL — resolve pronouns using context ──────────
        const std::string question = resolve_pronouns(raw_question);
        const std::vector<Entity> entities = NEREngine::extract(question);

        // ── Step 3: search ────────────────────────────────────────────
        std::vector<SearchResult> search_hits = omega_.search(question);
        std::vector<std::pair<TripleRecord, float>> semantic_hits =
            mesh_.semantic_recall(question, 8);

        // ── Step 4: relevance filter — discard low-scoring results ────
        const std::string q_lower = lower_copy(question);
        // keep only search hits whose topic or text actually overlaps query words
        std::vector<SearchResult> filtered_hits;
        filtered_hits.reserve(search_hits.size());
        for (const auto& hit : search_hits) {
            // at least one entity or keyword must appear in topic/text
            bool relevant = false;
            for (const auto& ent : entities) {
                if (lower_copy(hit.topic).find(lower_copy(ent.text)) != std::string::npos ||
                    lower_copy(hit.text).find(lower_copy(ent.text)) != std::string::npos) {
                    relevant = true;
                    break;
                }
            }
            // fallback: check query words individually (>4 chars)
            if (!relevant) {
                std::istringstream ss(q_lower);
                std::string tok;
                while (ss >> tok) {
                    if (tok.size() > 4 &&
                        (lower_copy(hit.topic).find(tok) != std::string::npos ||
                         lower_copy(hit.text).find(tok) != std::string::npos)) {
                        relevant = true;
                        break;
                    }
                }
            }
            if (relevant) filtered_hits.push_back(hit);
        }
        search_hits = filtered_hits;

        // ── Step 5: confidence ────────────────────────────────────────
        double best_entropy = 0.0;
        std::string most_uncertain = "knowledge";
        for (const Entity& entity : entities) {
            const double entropy = mesh_.local_entropy(entity.text);
            if (entropy > best_entropy) { best_entropy = entropy; most_uncertain = entity.text; }
        }

        double confidence = 0.0;
        if (!semantic_hits.empty())
            confidence = std::max(confidence, static_cast<double>(semantic_hits.front().second));
        if (!search_hits.empty())
            confidence = std::max(confidence, 0.5);

        if (search_hits.empty() && semantic_hits.empty()) {
            const std::string entity_hint = entities.empty() ? question : entities.front().text;
            out << "Mujhe '" << entity_hint << "' ke baare mein abhi kuch nahi pata.\n"
                << "  → learn " << entity_hint << "\n"
                << "  → deep " << entity_hint << "\n";
            omega_.log_query(question, 0, 0.0, false);
            if (context_window_.size() >= CTX_MAX) context_window_.pop_front();
            context_window_.push_back({raw_question, entity_hint});
            return out.str();
        }

        // ── Step 6: compose answer ────────────────────────────────────
        // Facts from search — show top 4 relevant sentences only
        if (!search_hits.empty()) {
            int shown = 0;
            for (const auto& hit : search_hits) {
                out << trim_copy(hit.text) << "\n";
                if (++shown >= 4) break;
            }
            out << "\n";
        }

        // Knowledge graph claims — max 4
        if (!semantic_hits.empty()) {
            out << "Knowledge graph:\n";
            int used = 0;
            for (const auto& hit : semantic_hits) {
                mesh_.mark_accessed(hit.first.id);
                out << "  " << hit.first.subject << " → " << hit.first.relation
                    << " → " << hit.first.object
                    << "  [certainty " << format_double(hit.first.certainty, 2) << "]\n";
                if (++used >= 4) break;
            }
            out << "\n";
        }

        // Reasoning chain between first two entities
        if (entities.size() >= 2) {
            auto path = hop_reasoner_.find(entities[0].text, entities[1].text, 4);
            if (path.has_value()) {
                out << "Reasoning chain:\n";
                for (const auto& step : path->steps) {
                    out << "  " << step.subject << " → " << step.relation
                        << " → " << step.object << "\n";
                }
                out << "  Confidence: " << format_double(path->confidence, 3) << "\n\n";
            }
        }

        // Contradictions — if any for this topic
        const auto contradictions = contradiction_detector_.scan(mesh_);
        bool disclosed = false;
        for (const auto& c : contradictions) {
            if (!entities.empty() &&
                (lower_copy(c.left_fact).find(lower_copy(entities[0].text)) != std::string::npos ||
                 lower_copy(c.right_fact).find(lower_copy(entities[0].text)) != std::string::npos)) {
                if (!disclosed) { out << "Contradictions found:\n"; disclosed = true; }
                out << "  ⚠ " << c.left_fact << " <-> " << c.right_fact << "\n";
            }
        }

        // Sources
        std::set<std::string> topics_used;
        for (const auto& h : search_hits) topics_used.insert(h.topic);
        if (!topics_used.empty()) {
            out << "\nSources: [";
            bool first = true;
            for (const auto& t : topics_used) {
                if (!first) out << ", "; first = false;
                out << t;
            }
            out << "]\n";
        }
        out << "Memory: "
            << omega_.sentence_count() << " sentences | "
            << mesh_.size() << " triples\n";

        omega_.log_query(question,
                         static_cast<int>(semantic_hits.size() + search_hits.size()),
                         confidence, confidence >= 0.45);

        // ── Step 7: update context window ────────────────────────────
        const std::string entity_for_ctx = dominant_entity(question, entities);
        if (context_window_.size() >= CTX_MAX) context_window_.pop_front();
        context_window_.push_back({raw_question, entity_for_ctx});

        return out.str();
    }

    std::string learn_topic(const std::string& topic) {
        ActionOutcome outcome = execute_crawl(topic, "USER");
        std::ostringstream out;
        out << "Learned topic: " << topic << "\n"
            << "  Pages fetched: " << outcome.pages_fetched << "\n"
            << "  Triples added: " << outcome.triples_added << "\n"
            << "  Reward: " << format_double(outcome.reward, 3) << "\n";
        if (!outcome.hypotheses.empty()) {
            out << "  New hypotheses:\n";
            for (const auto& item : outcome.hypotheses) {
                out << "    - " << item.record.subject << " --[" << item.record.relation
                    << "]--> " << item.record.object << " (" << item.classification
                    << ", conf " << format_double(item.record.confidence, 3) << ")\n";
            }
        }
        return out.str();
    }

    std::string run_hypothesis_cycle() {
        const std::vector<GeneratedHypothesis> generated = hypothesis_generator_.generate(12);
        std::ostringstream out;
        out << "Hypothesis cycle generated " << generated.size() << " candidates\n";
        for (const auto& item : generated) {
            out << "  - " << item.record.subject << " --[" << item.record.relation << "]--> "
                << item.record.object << " [trigger " << item.record.trigger_concept
                << ", conf " << format_double(item.record.confidence, 3)
                << ", status " << item.classification << "]\n";
        }
        out << "\nTracked hypotheses:\n";
        for (const auto& record : hypotheses_.top(15)) {
            out << "  - #" << record.id << " "
                << record.subject << " --[" << record.relation << "]--> " << record.object
                << " | conf " << format_double(record.confidence, 3)
                << " | status " << record.status
                << " | trigger " << record.trigger_concept;
            if (!record.evidence.empty()) {
                out << " | evidence " << record.evidence;
            }
            out << "\n";
        }
        return out.str();
    }

    std::string status_string() const {
        std::lock_guard<std::mutex> lock(state_mutex_);
        std::ostringstream out;
        out << "Sentences in FTS5: " << omega_.sentence_count() << "\n"
            << "Triples in mesh: " << mesh_.size() << "\n"
            << "Global entropy: " << format_double(last_hunger_.mesh_entropy, 3) << "\n";
        out << "Top hungriest concepts:\n";
        for (std::size_t i = 0; i < std::min<std::size_t>(3, last_hunger_.top_hungry.size()); ++i) {
            out << "  - " << last_hunger_.top_hungry[i].first << ": "
                << format_double(last_hunger_.top_hungry[i].second, 3) << "\n";
        }
        out << "Active hypotheses: " << hypotheses_.count_active() << "\n"
            << "Paradoxes: " << paradoxes_.count() << "\n"
            << "Uptime seconds: "
            << std::chrono::duration_cast<std::chrono::seconds>(
                   std::chrono::steady_clock::now() - startup_time_).count() << "\n"
            << "CPU: " << format_double(autonomic_.last_vitals.cpu_percent, 2) << "%\n"
            << "RAM free ratio: " << format_double(autonomic_.last_vitals.ram_free_ratio, 3) << "\n"
            << "Last tick ms: " << format_double(autonomic_.last_tick_ms, 2) << "\n";
        return out.str();
    }

    std::string agents_string() const {
        std::ostringstream out;
        const auto reports = shared_.reports();
        for (const auto& report : reports) {
            out << report.agent << ": " << report.action
                << " | triples " << report.triples_contributed
                << " | contradictions " << report.contradictions_found
                << " | reward " << format_double(report.reward, 3)
                << " | detail " << report.detail << "\n";
        }
        return out.str();
    }

    std::string paradoxes_string() const {
        std::ostringstream out;
        for (const auto& record : paradoxes_.list(20)) {
            out << record.subject << " --[" << record.relation << "]--> " << record.object
                << " | confidence " << format_double(record.confidence, 3)
                << " | discovered " << record.generated_at
                << " | reason " << record.evidence << "\n";
        }
        return out.str();
    }

    std::string semantic_string(const std::string& term) const {
        std::ostringstream out;
        const auto nearest = mesh_.nearest_concepts(term, 10);
        for (const auto& entry : nearest) {
            out << entry.first << " | cosine " << format_double(entry.second, 4) << "\n";
            for (const auto& triple : mesh_.triples_for_concept(entry.first, 3)) {
                out << "  - " << triple.subject << " --[" << triple.relation << "]--> "
                    << triple.object << " [w " << format_double(triple.weight, 2) << "]\n";
            }
        }
        return out.str();
    }

    std::string deduce_string(const std::string& subject, const std::string& relation) const {
        std::ostringstream out;
        const auto chains = cortex_.deduce(subject, relation, 4);
        for (const auto& chain : chains) {
            double confidence = 1.0;
            for (const auto& hop : chain) {
                confidence *= std::max(0.01, hop.confidence);
                out << hop.subject << " --[" << hop.relation << "]--> " << hop.object
                    << " [" << format_double(hop.confidence, 3) << "]\n";
            }
            out << "  chain confidence: " << format_double(confidence, 3) << "\n\n";
        }
        if (chains.empty()) {
            out << "No deduction chain found.\n";
        }
        return out.str();
    }

    std::string hop_string(const std::string& start, const std::string& target) const {
        std::ostringstream out;
        const auto path = hop_reasoner_.find(start, target, 5);
        if (!path.has_value()) {
            out << "No path found.\n";
            return out.str();
        }
        for (const auto& step : path->steps) {
            out << step.subject << " --[" << step.relation << "]--> " << step.object
                << " [" << format_double(step.confidence, 3) << "]\n";
        }
        out << "Path confidence: " << format_double(path->confidence, 3) << "\n";
        return out.str();
    }

    std::string contradictions_string() const {
        std::ifstream in("contradictions.log");
        if (!in) {
            return "No contradictions.log present.\n";
        }
        std::deque<std::string> tail;
        std::string line;
        while (std::getline(in, line)) {
            tail.push_back(line);
            if (tail.size() > 20) {
                tail.pop_front();
            }
        }
        std::ostringstream out;
        for (const auto& entry : tail) {
            out << entry << "\n";
        }
        return out.str();
    }

    std::string plan_and_execute(const std::string& description) {
        const GoalDescription goal = parse_goal(description);
        const PlanningState state = current_planning_state();
        const auto plan = planner_.plan(goal, state);
        if (plan.empty()) {
            return "Planner returned no executable steps.\n";
        }

        std::ostringstream out;
        out << "Plan for '" << description << "':\n";
        for (const auto& action : plan) {
            out << "  - " << action_name(action.kind);
            if (!action.target.empty()) {
                out << " " << action.target;
            }
            out << " (cost " << format_double(action.cost, 2) << ")\n";
        }
        out << "\nExecution:\n";
        for (const auto& action : plan) {
            ActionOutcome result = execute_planned_action(action, "USER_PLAN");
            out << "  - " << result.action << ": " << result.message
                << " [reward " << format_double(result.reward, 3) << "]\n";
        }
        return out.str();
    }

    bool save_snapshot(const std::string& path) const {
        const auto records = mesh_.loadable_records();
        std::ostringstream payload;
        payload << records.size() << "\n";
        for (const TripleRecord& record : records) {
            payload << std::quoted(record.subject) << " "
                    << std::quoted(record.relation) << " "
                    << std::quoted(record.object) << " "
                    << record.id << " "
                    << record.weight << " "
                    << record.certainty << " "
                    << record.first_seen << " "
                    << record.last_seen << " "
                    << record.last_access << " "
                    << record.access_count << " "
                    << (record.contradiction_flag ? 1 : 0) << " "
                    << (record.quarantined ? 1 : 0) << " "
                    << std::quoted(temporal_name(record.temporal)) << " "
                    << std::quoted(join_sources(record.sources)) << "\n";
        }
        const std::string body = payload.str();
        const std::string signature = receptor_.sign(body);
        std::ofstream out(path, std::ios::trunc);
        if (!out) {
            return false;
        }
        out << signature << "\n" << body;
        return out.good();
    }

    bool load_snapshot(const std::string& path) {
        std::ifstream in(path);
        if (!in) {
            return false;
        }
        std::string signature;
        if (!std::getline(in, signature)) {
            return false;
        }
        std::ostringstream body_stream;
        body_stream << in.rdbuf();
        const std::string body = body_stream.str();
        if (!receptor_.verify(body, signature)) {
            return false;
        }

        std::istringstream payload(body);
        std::size_t count = 0;
        payload >> count;
        payload.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        std::vector<TripleRecord> records;
        records.reserve(count);
        for (std::size_t i = 0; i < count; ++i) {
            TripleRecord record;
            std::string temporal;
            std::string sources;
            payload >> std::quoted(record.subject)
                    >> std::quoted(record.relation)
                    >> std::quoted(record.object)
                    >> record.id
                    >> record.weight
                    >> record.certainty
                    >> record.first_seen
                    >> record.last_seen
                    >> record.last_access
                    >> record.access_count;
            int contradiction = 0;
            int quarantined = 0;
            payload >> contradiction >> quarantined >> std::quoted(temporal) >> std::quoted(sources);
            payload.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
            record.contradiction_flag = contradiction != 0;
            record.quarantined = quarantined != 0;
            if (upper_copy(temporal) == "PAST") {
                record.temporal = TemporalState::Past;
            } else if (upper_copy(temporal) == "FUTURE") {
                record.temporal = TemporalState::Future;
            } else if (upper_copy(temporal) == "UNKNOWN") {
                record.temporal = TemporalState::Unknown;
            } else {
                record.temporal = TemporalState::Present;
            }
            record.sources = split_sources(sources);
            records.push_back(record);
        }

        mesh_.load_records(records);
        omega_.rewrite_triples(records);
        return true;
    }

    std::string identity_string() const {
        return MythosCore::identity_text(omega_.sentence_count(), mesh_.size(),
                                         offline_only_, response_mode_);
    }

    std::string why_string() const {
        std::ostringstream out;
        out << "Last answer audit\n";
        out << "Skill: " << last_answer_.skill;
        if (!last_answer_.skill.empty()) {
            out << " | " << SkillEngine::describe(last_answer_.skill);
        }
        out << "\n";
        out << "Intent: " << QueryParser::name(last_answer_.query.intent) << "\n";
        out << "Confidence: " << format_double(last_answer_.confidence, 3)
            << " | belief: " << last_answer_.belief_label
            << " (" << format_double(last_answer_.belief_score, 3) << ")"
            << " | verified: " << (last_answer_.verified ? "yes" : "no") << "\n";
        if (!last_answer_.query.resolved.empty()) {
            out << "Resolved query: " << last_answer_.query.resolved << "\n";
        }
        if (!last_answer_.evidence.empty()) {
            out << "\nEvidence:\n";
            int shown = 0;
            for (const EvidenceItem& item : last_answer_.evidence) {
                out << "  - " << item.text;
                if (!item.source.empty()) {
                    out << " | source " << item.source;
                }
                out << " | score " << format_double(item.score, 3)
                    << " | certainty " << format_double(item.certainty, 3) << "\n";
                if (++shown >= 8) {
                    break;
                }
            }
        }
        if (!last_answer_.reasoning_steps.empty()) {
            out << "\nReasoning path:\n";
            for (const std::string& step : last_answer_.reasoning_steps) {
                out << "  - " << step << "\n";
            }
        }
        if (!last_answer_.caveats.empty()) {
            out << "\nCaveats:\n";
            for (const std::string& caveat : last_answer_.caveats) {
                out << "  - " << caveat << "\n";
            }
        }
        if (!last_answer_.critic_notes.empty()) {
            out << "\nCritic notes:\n";
            for (const std::string& note : last_answer_.critic_notes) {
                out << "  - " << note << "\n";
            }
        }
        return out.str();
    }

    std::string gaps_string() const {
        std::ostringstream out;
        out << "Knowledge gaps queued by strict verifier:\n";
        if (knowledge_gaps_.empty()) {
            out << "  (none in this session)\n";
            return out.str();
        }
        for (const std::string& gap : knowledge_gaps_) {
            out << "  - " << gap << "\n";
        }
        return out.str();
    }

    std::string set_offline_mode(const std::string& value) {
        const std::string mode = lower_copy(trim_copy(value));
        if (mode == "on" || mode == "true" || mode == "1") {
            offline_only_ = true;
            std::lock_guard<std::mutex> lock(state_mutex_);
            autonomic_.pause_learning = true;
        } else if (mode == "off" || mode == "false" || mode == "0") {
            offline_only_ = false;
            std::lock_guard<std::mutex> lock(state_mutex_);
            autonomic_.pause_learning = false;
        }
        return std::string("Offline answering: ") + (offline_only_ ? "ON" : "OFF") + "\n";
    }

    std::string set_response_mode(const std::string& value) {
        const std::string mode = lower_copy(trim_copy(value));
        if (GPTStyleCortex::valid_mode(mode)) {
            response_mode_ = mode;
        }
        return "Response mode: " + response_mode_ + " | shape: " +
               GPTStyleCortex::answer_shape(response_mode_) + "\n";
    }

    std::string import_path(const std::string& path_text) {
        const fs::path root = fs::path(trim_copy(path_text));
        std::ostringstream out;
        if (root.empty() || !fs::exists(root)) {
            return "Import failed: path not found.\n";
        }
        int files = 0;
        int triples = 0;
        auto import_one = [&](const fs::path& file) {
            if (!KnowledgeGrowthEngine::supported_import_extension(file)) {
                return;
            }
            std::ifstream in(file, std::ios::binary);
            if (!in) {
                return;
            }
            std::ostringstream buffer;
            buffer << in.rdbuf();
            std::string text = trim_copy(buffer.str());
            if (text.size() < 24) {
                return;
            }
            const std::string title = file.stem().string();
            const std::string source = "file://" + file.string();
            omega_.store_page(title, title, text, source, {}, "local_corpus");
            triples += ingest_text_knowledge(title, text, "LOCAL_CORPUS");
            ++files;
        };

        if (fs::is_regular_file(root)) {
            import_one(root);
        } else {
            for (const auto& entry : fs::recursive_directory_iterator(root)) {
                if (entry.is_regular_file()) {
                    import_one(entry.path());
                }
            }
        }
        out << "Imported " << files << " file(s), added " << triples
            << " knowledge triples. Answers can now use this offline.\n";
        return out.str();
    }

    std::string teach_fact(const std::string& spec) {
        const auto parts = split_pipe_fields(spec);
        if (parts.size() != 3) {
            return "Usage: teach <subject>|<relation>|<object>\n";
        }
        const UpsertResult upsert = mesh_.upsert(parts[0], upper_copy(parts[1]), parts[2],
                                                 "USER_TEACH", 0.92f);
        if (upsert.id < 0) {
            return "Teach failed: mesh is full or record was rejected.\n";
        }
        persist_one(upsert.id);
        shared_.publish_fact(upsert.id);
        dirty_state_.store(true);
        std::ostringstream out;
        out << "Taught: " << parts[0] << " --[" << upper_copy(parts[1]) << "]--> "
            << parts[2] << "\n";
        out << "Verifier note: user-taught fact stored with source USER_TEACH.\n";
        return out.str();
    }

    std::string recall_memory(const std::string& query) const {
        std::ostringstream out;
        out << "Local recall for: " << query << "\n";
        int shown = 0;
        for (const SearchResult& hit : omega_.search(query, 8)) {
            out << "  - " << hit.text << " | " << hit.topic;
            if (!hit.source_url.empty()) {
                out << " | " << hit.source_url;
            }
            out << "\n";
            if (++shown >= 5) {
                break;
            }
        }
        const auto triples = mesh_.semantic_recall(query, 6);
        if (!triples.empty()) {
            out << "Graph recall:\n";
            int used = 0;
            for (const auto& hit : triples) {
                out << "  - " << hit.first.subject << " --[" << hit.first.relation
                    << "]--> " << hit.first.object
                    << " | score " << format_double(hit.second, 3) << "\n";
                if (++used >= 5) {
                    break;
                }
            }
        }
        if (shown == 0 && triples.empty()) {
            out << "  (no local recall hits)\n";
        }
        return out.str();
    }

    std::string forget_gap(const std::string& target) {
        const std::string clean = trim_copy(target);
        if (clean.empty()) {
            return "Usage: forgetgap <topic|all>\n";
        }
        if (lower_copy(clean) == "all") {
            const std::size_t removed = knowledge_gaps_.size();
            knowledge_gaps_.clear();
            return "Cleared " + std::to_string(removed) + " knowledge gap(s).\n";
        }
        const std::size_t before = knowledge_gaps_.size();
        knowledge_gaps_.erase(
            std::remove_if(knowledge_gaps_.begin(), knowledge_gaps_.end(),
                           [&](const std::string& gap) {
                               return lower_copy(gap) == lower_copy(clean);
                           }),
            knowledge_gaps_.end());
        return "Removed " + std::to_string(before - knowledge_gaps_.size()) + " matching gap(s).\n";
    }

    std::string export_knowledge(const std::string& path_text) const {
        const std::string path = trim_copy(path_text).empty() ? "infinity_export.tsv" : trim_copy(path_text);
        std::ofstream out_file(path);
        if (!out_file) {
            return "Export failed: could not open output file.\n";
        }
        out_file << "subject\trelation\tobject\tcertainty\tweight\tsources\n";
        std::size_t count = 0;
        for (const TripleRecord& record : mesh_.snapshot()) {
            out_file << record.subject << "\t"
                     << record.relation << "\t"
                     << record.object << "\t"
                     << format_double(record.certainty, 3) << "\t"
                     << format_double(record.weight, 3) << "\t"
                     << join_sources(record.sources) << "\n";
            ++count;
        }
        return "Exported " + std::to_string(count) + " triples to " + path + "\n";
    }

    std::string self_test_string() const {
        std::ostringstream out;
        out << "INFINITY self-test\n";
        out << "  QueryParser: " << (QueryParser::parse("India kya hai?", "India kya hai?").intent == QueryIntent::Definition ? "ok" : "check") << "\n";
        out << "  SkillEngine: " << (SkillEngine::route(QueryParser::parse("why quantum physics", "why quantum physics")).empty() ? "check" : "ok") << "\n";
        out << "  GPTStyleCortex modes: " << (GPTStyleCortex::valid_mode(response_mode_) ? "ok" : "check") << "\n";
        out << "  Memory DB: " << omega_.sentence_count() << " sentences\n";
        out << "  Mesh: " << mesh_.size() << " triples\n";
        out << "  Offline mode: " << (offline_only_ ? "ON" : "OFF") << "\n";
        out << "  Last skill: " << last_answer_.skill << "\n";
        out << "  Last belief: " << last_answer_.belief_label
            << " (" << format_double(last_answer_.belief_score, 3) << ")\n";
        out << "  Last answer verified: " << (last_answer_.verified ? "yes" : "no") << "\n";
        out << "  Gaps: " << knowledge_gaps_.size() << "\n";
        return out.str();
    }

    std::string skills_string() const {
        std::ostringstream out;
        out << "Skill Engine routes:\n";
        for (const std::string& skill : SkillEngine::available()) {
            out << "  - " << skill << ": " << SkillEngine::describe(skill) << "\n";
        }
        return out.str();
    }

    std::string belief_string() const {
        std::ostringstream out;
        out << "Belief System\n";
        out << "  Last belief: " << last_answer_.belief_label
            << " (" << format_double(last_answer_.belief_score, 3) << ")\n";
        out << "  Confidence: " << format_double(last_answer_.confidence, 3) << "\n";
        out << "  Evidence items: " << last_answer_.evidence.size() << "\n";
        out << "  Sources: " << last_answer_.sources.size() << "\n";
        out << "  Rule: strong >= 0.78, moderate >= 0.55, weak >= 0.35, else unverified.\n";
        return out.str();
    }

    std::string critic_string() const {
        std::ostringstream out;
        out << "Answer Critic\n";
        if (last_answer_.critic_notes.empty()) {
            out << "  Last answer passed critic checks.\n";
        } else {
            for (const std::string& note : last_answer_.critic_notes) {
                out << "  - " << note << "\n";
            }
        }
        return out.str();
    }

private:
    struct IngestResult {
        int triples_added{0};
        bool pruned{false};
    };

    std::string answer_question_v55(const std::string& raw_question) {
        const std::string resolved = resolve_pronouns(raw_question);
        ParsedQuery query = QueryParser::parse(raw_question, resolved);

        if (query.intent == QueryIntent::Greeting) {
            update_context(raw_question, {});
            return "Namaste. INFINITY v5.5 online hai: strict verifier, local memory, Hinglish-first. "
                   "Seedha sawaal poochho, ya `learn <topic>` / `import <path>` se memory grow karo.";
        }

        if (query.intent == QueryIntent::SelfQuery) {
            update_context(raw_question, {});
            return identity_string();
        }

        AnswerPlan plan = query.intent == QueryIntent::Planning
            ? build_planning_answer(query)
            : build_answer_plan(query);
        BeliefSystem::apply(plan);
        StrictVerifier::verify(plan);
        AnswerCritic::review(plan);
        if (!plan.verified) {
            remember_gap(query);
        }

        last_answer_ = plan;
        update_context(raw_question, dominant_entity(query.resolved, query.entities));
        omega_.log_query(query.resolved, static_cast<int>(plan.evidence.size()), plan.confidence, plan.verified);
        return MythosCore::compose(plan, response_mode_);
    }

    AnswerPlan build_planning_answer(const ParsedQuery& query) {
        AnswerPlan plan;
        plan.query = query;
        plan.skill = SkillEngine::route(query);
        const std::string target = query.entities.empty() ? "is goal" : query.entities.front().text;
        plan.direct = "Plan: pehle target ko define karo, phir local evidence collect karo, "
                      "phir contradictions verify karke answer/test loop chalao.";
        plan.bullets = {
            "Goal lock: " + target,
            "Knowledge grow: `learn " + target + "` ya `import <path>`",
            "Verify: `why`, `contradictions`, aur `gaps` se audit karo"
        };
        plan.reasoning_steps = {
            "Planner ne user intent ko task/roadmap maana.",
            "Strict verifier ke liye har step evidence-producing hai.",
            "Online learning sirf explicit command se trigger hogi."
        };
        plan.evidence.push_back({"Built-in agent planning policy", target, "PLANNED_AS", "VERIFIABLE_STEPS",
                                 "INFINITY_POLICY", 0.72, 0.80, true});
        plan.sources.insert("INFINITY_POLICY");
        return plan;
    }

    AnswerPlan build_answer_plan(const ParsedQuery& query) {
        AnswerPlan plan;
        plan.query = query;
        plan.skill = SkillEngine::route(query);
        plan.evidence = collect_evidence(query);
        std::sort(plan.evidence.begin(), plan.evidence.end(),
                  [](const EvidenceItem& a, const EvidenceItem& b) {
                      return (a.score + a.certainty) > (b.score + b.certainty);
                  });

        if (plan.evidence.empty()) {
            return plan;
        }

        const EvidenceItem& top = plan.evidence.front();
        if (query.intent == QueryIntent::Opinion) {
            plan.direct = "Isme judgement nahi dunga. Verified facts ke basis par: " + top.text;
            plan.caveats.push_back("Opinion request ko neutral factual mode mein answer kiya gaya.");
        } else if (query.intent == QueryIntent::Relation && top.graph_fact) {
            plan.direct = "Relation: " + top.subject + " --[" + top.relation + "]--> " + top.object + ".";
        } else if (query.intent == QueryIntent::Cause) {
            plan.direct = "Reason/evidence: " + top.text;
        } else if (query.intent == QueryIntent::Comparison) {
            plan.direct = "Comparison ke liye local evidence mila. Sabse relevant point: " + top.text;
        } else {
            plan.direct = "Seedha jawab: " + top.text;
        }

        int bullet_count = 0;
        for (const EvidenceItem& item : plan.evidence) {
            if (item.text == top.text && bullet_count > 0) {
                continue;
            }
            plan.bullets.push_back(item.text);
            if (!item.source.empty()) {
                plan.sources.insert(item.source);
            }
            if (++bullet_count >= 3) {
                break;
            }
        }

        if (query.entities.size() >= 2) {
            const auto path = hop_reasoner_.find(query.entities[0].text, query.entities[1].text, 4);
            if (path.has_value()) {
                for (const auto& step : path->steps) {
                    plan.reasoning_steps.push_back(step.subject + " --[" + step.relation + "]--> " + step.object);
                }
                plan.evidence.push_back({"Graph path confidence " + format_double(path->confidence, 3),
                                         query.entities[0].text, "PATH_TO", query.entities[1].text,
                                         "KNOWLEDGE_MESH", path->confidence, path->confidence, true});
            }
        }

        const auto contradictions = contradiction_detector_.scan(mesh_);
        for (const auto& c : contradictions) {
            if (!query.entities.empty() &&
                (lower_copy(c.left_fact).find(lower_copy(query.entities[0].text)) != std::string::npos ||
                 lower_copy(c.right_fact).find(lower_copy(query.entities[0].text)) != std::string::npos)) {
                plan.caveats.push_back("Contradiction present: " + c.left_fact + " <-> " + c.right_fact);
                break;
            }
        }
        return plan;
    }

    std::vector<EvidenceItem> collect_evidence(const ParsedQuery& query) {
        std::vector<EvidenceItem> evidence;
        const std::string search_query = best_search_query(query);
        for (const SearchResult& hit : omega_.search(search_query, 12)) {
            const double score = score_search_hit(query, hit);
            if (score < 0.22) {
                continue;
            }
            evidence.push_back({trim_copy(hit.text), hit.topic, "MENTIONS", hit.topic,
                                hit.source_url.empty() ? hit.topic : hit.source_url,
                                score, 0.58, false});
        }

        for (const auto& hit : mesh_.semantic_recall(query.resolved, 10)) {
            const TripleRecord& triple = hit.first;
            const double score = score_triple_hit(query, triple, hit.second);
            if (score < 0.25) {
                continue;
            }
            mesh_.mark_accessed(triple.id);
            evidence.push_back({triple.subject + " --[" + triple.relation + "]--> " + triple.object,
                                triple.subject, triple.relation, triple.object,
                                triple.sources.empty() ? "KNOWLEDGE_MESH" : *triple.sources.begin(),
                                score, triple.certainty, true});
        }
        return evidence;
    }

    std::string best_search_query(const ParsedQuery& query) const {
        if (!query.entities.empty()) {
            return query.entities.front().text;
        }
        return query.resolved;
    }

    double score_search_hit(const ParsedQuery& query, const SearchResult& hit) const {
        const std::string hay = lower_copy(hit.topic + " " + hit.text);
        double score = 0.15 + clamp_double(hit.score, 0.0, 1.0) * 0.20;
        for (const Entity& entity : query.entities) {
            if (hay.find(lower_copy(entity.text)) != std::string::npos) {
                score += 0.35;
            }
        }
        for (const std::string& token : split_words(query.normalized)) {
            if (token.size() > 4 && hay.find(token) != std::string::npos) {
                score += 0.04;
            }
        }
        if (query.intent == QueryIntent::Definition &&
            (hay.find(" is ") != std::string::npos || hay.find(" are ") != std::string::npos)) {
            score += 0.10;
        }
        return clamp_double(score, 0.0, 1.0);
    }

    double score_triple_hit(const ParsedQuery& query, const TripleRecord& triple, float semantic_score) const {
        const std::string hay = lower_copy(triple.subject + " " + triple.relation + " " + triple.object);
        double score = 0.18 + clamp_double((static_cast<double>(semantic_score) + 1.0) * 0.20, 0.0, 0.40);
        for (const Entity& entity : query.entities) {
            if (hay.find(lower_copy(entity.text)) != std::string::npos) {
                score += 0.28;
            }
        }
        for (const std::string& hint : query.relation_hints) {
            if (lower_copy(triple.relation).find(lower_copy(hint)) != std::string::npos) {
                score += 0.18;
            }
        }
        if (triple.contradiction_flag || triple.quarantined) {
            score -= 0.35;
        }
        return clamp_double(score, 0.0, 1.0);
    }

    void remember_gap(const ParsedQuery& query) {
        std::string gap = query.entities.empty() ? trim_copy(query.resolved) : query.entities.front().text;
        if (gap.empty()) {
            gap = "unknown query";
        }
        if (std::find(knowledge_gaps_.begin(), knowledge_gaps_.end(), gap) == knowledge_gaps_.end()) {
            knowledge_gaps_.push_back(gap);
            if (knowledge_gaps_.size() > 50) {
                knowledge_gaps_.pop_front();
            }
        }
    }

    void update_context(const std::string& user_input, const std::string& entity) {
        if (context_window_.size() >= CTX_MAX) {
            context_window_.pop_front();
        }
        context_window_.push_back({user_input, entity});
    }

    int ingest_text_knowledge(const std::string& topic, const std::string& text, const std::string& source_tag) {
        int added = 0;
        auto add_triple = [&](const std::string& subject,
                              const std::string& relation,
                              const std::string& object,
                              float certainty) {
            const std::string clean_subject = trim_copy(subject);
            const std::string clean_relation = trim_copy(relation);
            const std::string clean_object = trim_copy(object);
            if (clean_subject.empty() || clean_relation.empty() || clean_object.empty()) {
                return;
            }
            const UpsertResult upsert = mesh_.upsert(clean_subject, clean_relation, clean_object,
                                                     source_tag, certainty);
            if (upsert.id >= 0) {
                persist_one(upsert.id);
                if (upsert.inserted) {
                    ++added;
                    shared_.publish_fact(upsert.id);
                    dirty_state_.store(true);
                }
            }
        };

        const auto sentences = split_sentences(text);
        if (!sentences.empty()) {
            const std::string first = trim_copy(sentences.front());
            std::smatch match;
            static const std::regex definition(R"(\b(is|are|was|were)\s+(an?\s+|the\s+)?([^.;]{3,120}))",
                                               std::regex_constants::icase);
            if (std::regex_search(first, match, definition) && match.size() >= 4) {
                add_triple(topic, "IS_A", trim_copy(match[3].str()), 0.76f);
            }
        }

        static const std::vector<std::pair<std::regex, std::string>> patterns = {
            {std::regex(R"(\bfounded by\s+([A-Z][A-Za-z0-9 .,'-]{2,80}))", std::regex_constants::icase), "FOUNDED_BY"},
            {std::regex(R"(\bfounded in\s+([0-9]{3,4}))", std::regex_constants::icase), "FOUNDED_IN"},
            {std::regex(R"(\bestablished in\s+([0-9]{3,4}))", std::regex_constants::icase), "ESTABLISHED_IN"},
            {std::regex(R"(\blocated in\s+([A-Z][A-Za-z0-9 .,'-]{2,80}))", std::regex_constants::icase), "LOCATED_IN"},
            {std::regex(R"(\bborn in\s+([A-Z][A-Za-z0-9 .,'-]{2,80}))", std::regex_constants::icase), "BORN_IN"},
            {std::regex(R"(\bpart of\s+([A-Z][A-Za-z0-9 .,'-]{2,80}))", std::regex_constants::icase), "PART_OF"},
            {std::regex(R"(\bused for\s+([^.;]{3,100}))", std::regex_constants::icase), "USED_FOR"},
            {std::regex(R"(\bcaused by\s+([^.;]{3,100}))", std::regex_constants::icase), "CAUSED_BY"},
            {std::regex(R"(\balso known as\s+([^.;]{3,100}))", std::regex_constants::icase), "ALIAS_OF"}
        };

        for (const std::string& sentence : sentences) {
            for (const auto& pattern : patterns) {
                std::smatch match;
                if (std::regex_search(sentence, match, pattern.first) && match.size() >= 2) {
                    add_triple(topic, pattern.second, trim_copy(match[1].str()), 0.70f);
                }
            }
        }

        for (const Entity& entity : NEREngine::extract(text)) {
            if (entity.text.size() >= 4 && lower_copy(entity.text) != lower_copy(topic)) {
                add_triple(entity.text, "FOUND_IN", topic, 0.55f);
            }
        }
        return added;
    }

    static std::vector<std::string> split_pipe_fields(const std::string& spec) {
        std::vector<std::string> fields;
        std::string current;
        for (char c : spec) {
            if (c == '|') {
                fields.push_back(trim_copy(current));
                current.clear();
            } else {
                current.push_back(c);
            }
        }
        fields.push_back(trim_copy(current));
        fields.erase(std::remove_if(fields.begin(), fields.end(),
                                    [](const std::string& item) { return item.empty(); }),
                     fields.end());
        return fields;
    }

    void resilient_loop(const std::string& name, const std::function<void()>& loop) {
        while (running_.load()) {
            try {
                loop();
                return;
            } catch (const std::exception& ex) {
                Logger::console(name, std::string("worker exception: ") + ex.what(), COLOR_RED);
                std::this_thread::sleep_for(std::chrono::seconds(1));
            } catch (...) {
                Logger::console(name, "worker exception: unknown", COLOR_RED);
                std::this_thread::sleep_for(std::chrono::seconds(1));
            }
        }
    }

    void seed_topics_if_needed() {
        if (omega_.topic_count() > 0 || mesh_.size() > 0) {
            return;
        }
        const std::vector<std::string> seeds = {
            "Quantum entanglement", "Physics", "Mathematics", "Biology",
            "Chemistry", "Computer science", "History", "Philosophy", "Astronomy"
        };
        for (const std::string& topic : seeds) {
            enqueue_topic(topic);
        }
    }

    void enqueue_topic(const std::string& topic) {
        std::lock_guard<std::mutex> lock(queue_mutex_);
        const std::string lowered = lower_copy(topic);
        if (queued_topics_.insert(lowered).second) {
            topic_queue_.push_back(topic);
            queue_cv_.notify_one();
        }
    }

    std::optional<std::string> dequeue_topic(std::chrono::milliseconds timeout) {
        std::unique_lock<std::mutex> lock(queue_mutex_);
        queue_cv_.wait_for(lock, timeout, [&]() {
            return !topic_queue_.empty() || !running_.load();
        });
        if (topic_queue_.empty()) {
            return std::nullopt;
        }
        std::string topic = topic_queue_.front();
        topic_queue_.pop_front();
        queued_topics_.erase(lower_copy(topic));
        return topic;
    }

    IngestResult ingest_page(const WikiPage& page, const std::string& source_tag) {
        IngestResult result;
        if (!page.ok) {
            return result;
        }

        const std::string category = derive_category(page.title, page.summary);
        omega_.store_page(page.title, page.title, page.summary, page.url, page.links, category);
        result.triples_added += ingest_text_knowledge(page.title, page.summary, source_tag + ":rules");

        auto add_triple = [&](const std::string& subject,
                              const std::string& relation,
                              const std::string& object,
                              float certainty) {
            if (subject.empty() || relation.empty() || object.empty()) {
                return;
            }
            const UpsertResult upsert = mesh_.upsert(subject, relation, object, source_tag, certainty);
            if (upsert.id < 0) {
                return;
            }
            persist_one(upsert.id);
            if (upsert.pruned > 0) {
                result.pruned = true;
            }
            if (upsert.inserted) {
                result.triples_added += 1;
                shared_.publish_fact(upsert.id);
                dirty_state_.store(true);
            }
        };

        add_triple(page.title, "IS_A", upper_copy(category), 0.82f);
        add_triple(page.title, "CRAWLED_FROM", "WIKIPEDIA", 0.95f);
        if (lower_copy(page.topic) != lower_copy(page.title)) {
            add_triple(page.topic, "ALIAS_OF", page.title, 0.90f);
        }
        for (const std::string& link : page.links) {
            add_triple(page.title, "RELATES_TO", link, 0.68f);
        }
        for (const Entity& entity : NEREngine::extract(page.summary)) {
            if (entity.text.size() < 4 || lower_copy(entity.text) == lower_copy(page.title)) {
                continue;
            }
            add_triple(entity.text, "FOUND_IN", page.title, 0.62f);
        }
        return result;
    }

    void persist_one(int64_t id) {
        const auto record = mesh_.get_by_id(id);
        if (record.has_value()) {
            omega_.persist_triple(*record);
        }
    }

    void persist_all() {
        omega_.rewrite_triples(mesh_.snapshot());
    }

    ActionOutcome execute_crawl(const std::string& topic, const std::string& actor) {
        ActionOutcome outcome;
        outcome.action = "CRAWL_TOPIC " + topic;

        {
            std::lock_guard<std::mutex> lock(state_mutex_);
            if (autonomic_.pause_learning || !autonomic_.last_vitals.network_available) {
                outcome.message = "learning paused by medulla reflex";
                return outcome;
            }
        }

        const double entropy_before = mesh_.local_entropy(topic);
        const int threads = current_crawler_threads();
        HyperCrawler::CrawlReport report = HyperCrawler::crawl_topic(topic, threads, 1, 10);
        outcome.pages_fetched = report.pages_fetched;

        bool full_rewrite_needed = false;
        for (const WikiPage& page : report.pages) {
            IngestResult ingest = ingest_page(page, actor + ":" + topic);
            outcome.triples_added += ingest.triples_added;
            if (ingest.pruned) {
                full_rewrite_needed = true;
            }
        }

        run_limbic_consolidation(shared_.drain_new_facts());
        if (full_rewrite_needed) {
            persist_all();
        }

        const double entropy_after = mesh_.local_entropy(topic);
        omega_.record_crawl(topic, outcome.pages_fetched, outcome.triples_added,
                            entropy_before, entropy_after, report.duration_seconds);
        Logger::append_file("crawl_history.log",
            now_string() + " actor=" + actor + " topic=" + topic +
            " pages=" + std::to_string(outcome.pages_fetched) +
            " triples=" + std::to_string(outcome.triples_added) +
            " entropy_before=" + format_double(entropy_before, 3) +
            " entropy_after=" + format_double(entropy_after, 3) +
            " duration=" + format_double(report.duration_seconds, 3));

        if (outcome.triples_added > 0) {
            outcome.hypotheses = hypothesis_generator_.generate(3);
        }
        outcome.ok = true;
        outcome.reward = outcome.triples_added / std::max(0.25, report.duration_seconds);
        outcome.message = "fetched " + std::to_string(outcome.pages_fetched) +
                          " pages, added " + std::to_string(outcome.triples_added) + " triples";
        return outcome;
    }

    ActionOutcome verify_oldest_hypothesis(const std::string& actor) {
        ActionOutcome outcome;
        outcome.action = "VERIFY_HYPOTHESIS";
        const auto candidate = hypotheses_.oldest_candidate();
        if (!candidate.has_value()) {
            outcome.message = "no candidate hypothesis";
            return outcome;
        }

        const VerificationResult internal = verifier_.verify(
            candidate->subject, candidate->relation, candidate->object);
        if (!internal.is_valid && !internal.contradiction_ids.empty()) {
            hypotheses_.update_status(candidate->id, "REFUTED", internal.reason);
            outcome.ok = true;
            outcome.reward = 0.1;
            outcome.message = "refuted by internal contradiction";
            return outcome;
        }

        const WikiPage subject_page = HyperCrawler::fetch_page(candidate->subject);
        const WikiPage object_page = HyperCrawler::fetch_page(candidate->object);
        const std::string combined = lower_copy(subject_page.summary + " " + object_page.summary);
        const std::string object_lower = lower_copy(candidate->object);
        const std::string subject_lower = lower_copy(candidate->subject);

        const bool subject_mentions_object = combined.find(object_lower) != std::string::npos;
        const bool object_mentions_subject = combined.find(subject_lower) != std::string::npos;
        bool relation_evidence = false;
        for (const std::string& token : split_words(candidate->relation)) {
            if (token.size() >= 4 && combined.find(token) != std::string::npos) {
                relation_evidence = true;
                break;
            }
        }
        if (lower_copy(candidate->relation).find("relates") != std::string::npos) {
            relation_evidence = true;
        }

        if ((subject_mentions_object || object_mentions_subject) && relation_evidence) {
            hypotheses_.update_status(candidate->id, "PROMOTED",
                                      "wikipedia evidence from " + candidate->subject + " and " + candidate->object);
            const UpsertResult upsert = mesh_.upsert(candidate->subject, candidate->relation, candidate->object,
                                                     actor + ":hypothesis", static_cast<float>(candidate->confidence));
            if (upsert.id >= 0) {
                persist_one(upsert.id);
                if (upsert.inserted) {
                    shared_.publish_fact(upsert.id);
                }
                if (upsert.pruned > 0) {
                    persist_all();
                }
            }
            outcome.ok = true;
            outcome.reward = 1.0;
            outcome.message = "promoted candidate with live evidence";
        } else {
            hypotheses_.update_status(candidate->id, "CANDIDATE", "no supporting evidence yet");
            outcome.ok = true;
            outcome.reward = 0.05;
            outcome.message = "candidate still unresolved";
        }
        return outcome;
    }

    ActionOutcome run_contradiction_sweep() {
        ActionOutcome outcome;
        outcome.action = "CONTRADICTION_SWEEP";
        const auto contradictions = contradiction_detector_.scan(mesh_);
        for (const auto& contradiction : contradictions) {
            const std::string key = std::to_string(std::min(contradiction.left_id, contradiction.right_id)) + ":" +
                                    std::to_string(std::max(contradiction.left_id, contradiction.right_id));
            {
                std::lock_guard<std::mutex> lock(contradiction_mutex_);
                if (!seen_contradictions_.insert(key).second) {
                    continue;
                }
            }
            mesh_.flag_contradiction(contradiction.left_id, true);
            mesh_.flag_contradiction(contradiction.right_id, true);
            mesh_.scale_certainty(contradiction.left_id, 0.80f);
            mesh_.scale_certainty(contradiction.right_id, 0.80f);
            shared_.publish_fact(contradiction.left_id);
            shared_.publish_fact(contradiction.right_id);
            persist_one(contradiction.left_id);
            persist_one(contradiction.right_id);
            outcome.contradictions_found += 1;
            Logger::append_file("contradictions.log",
                now_string() + " " + contradiction.left_fact + " <-> " +
                contradiction.right_fact + " | " + contradiction.reason);
        }
        outcome.ok = true;
        outcome.reward = outcome.contradictions_found * 0.2;
        outcome.message = "found " + std::to_string(outcome.contradictions_found) + " contradictions";
        if (outcome.contradictions_found > 0) {
            dirty_state_.store(true);
        }
        return outcome;
    }

    ActionOutcome consolidate_memory() {
        ActionOutcome outcome;
        outcome.action = "CONSOLIDATE_MEMORY";
        const auto stats = mesh_.optimizer_pass();
        persist_all();
        omega_.vacuum();
        dirty_state_.store(false);
        outcome.ok = true;
        outcome.reward = static_cast<double>(stats.strengthened + stats.merged) * 0.02;
        outcome.message = "strengthened " + std::to_string(stats.strengthened) +
                          ", decayed " + std::to_string(stats.decayed) +
                          ", merged " + std::to_string(stats.merged);
        return outcome;
    }

    ActionOutcome execute_planned_action(const PlannedAction& action, const std::string& actor) {
        switch (action.kind) {
            case ActionKind::CrawlTopic:
                return execute_crawl(action.target, actor);
            case ActionKind::ConsolidateMemory:
                return consolidate_memory();
            case ActionKind::VerifyHypothesis:
                return verify_oldest_hypothesis(actor);
            case ActionKind::ContradictionSweep:
                return run_contradiction_sweep();
            case ActionKind::SaveState: {
                ActionOutcome outcome;
                outcome.action = "SAVE_STATE";
                outcome.ok = save_snapshot("infinity_state.snapshot");
                outcome.reward = outcome.ok ? 0.15 : 0.0;
                outcome.message = outcome.ok ? "snapshot saved" : "snapshot save failed";
                if (outcome.ok) {
                    dirty_state_.store(false);
                }
                return outcome;
            }
        }
        return {};
    }

    void run_limbic_consolidation(const std::vector<int64_t>& ids) {
        limbic_.consolidate(mesh_, ids, [this](int64_t id) { persist_one(id); });
    }

    PlanningState current_planning_state() const {
        std::lock_guard<std::mutex> lock(state_mutex_);
        PlanningState state;
        state.network_available = autonomic_.last_vitals.network_available;
        state.pause_learning = autonomic_.pause_learning;
        state.dirty_state = dirty_state_.load();
        state.has_candidate_hypothesis = hypotheses_.oldest_candidate().has_value();
        state.contradiction_backlog = !contradiction_detector_.scan(mesh_).empty();
        state.cpu_percent = autonomic_.last_vitals.cpu_percent;
        state.hunger = last_hunger_.curiosity_hunger;
        return state;
    }

    GoalDescription parse_goal(const std::string& description) const {
        const std::string lowered = lower_copy(trim_copy(description));
        if (lowered.rfind("learn ", 0) == 0) {
            return {description, "learn", trim_copy(description.substr(6))};
        }
        if (lowered.rfind("verify", 0) == 0) {
            return {description, "verify", ""};
        }
        if (lowered.rfind("save", 0) == 0) {
            return {description, "save", ""};
        }
        if (lowered.find("stabil") != std::string::npos || lowered.find("consolidate") != std::string::npos) {
            return {description, "stabilize", ""};
        }
        return {description, "learn", trim_copy(description)};
    }

    int current_crawler_threads() const {
        std::lock_guard<std::mutex> lock(state_mutex_);
        return autonomic_.crawler_threads;
    }

    void consciousness_loop() {
        while (running_.load()) {
            const auto tick_start = std::chrono::steady_clock::now();

            Vitals vitals = medulla_.pulse();
            HungerState hunger = hypothalamus_.compute(mesh_, omega_);
            {
                std::lock_guard<std::mutex> lock(state_mutex_);
                last_hunger_ = hunger;
                medulla_.handle_reflex(vitals, autonomic_);
            }

            const PlanningState state = current_planning_state();
            const FrontalDecision decision = frontal_.analyze(state, hunger, mesh_, omega_, planner_);
            if (!decision.candidate_topics.empty()) {
                std::vector<std::string> action_keys;
                std::vector<PlannedAction> plan = decision.plan;
                for (const PlannedAction& action : plan) {
                    if (action.kind == ActionKind::CrawlTopic) {
                        action_keys.push_back("CRAWL:" + action.target);
                    } else {
                        action_keys.push_back(action_name(action.kind));
                    }
                }

                const std::string category = omega_.topic_category(decision.primary_concept);
                const auto [chosen, explored] = q_table_.choose(category, action_keys, rng_);
                (void)explored;
                for (const PlannedAction& action : plan) {
                    const std::string key = action.kind == ActionKind::CrawlTopic
                        ? "CRAWL:" + action.target
                        : action_name(action.kind);
                    if (key == chosen) {
                        ActionOutcome outcome = execute_planned_action(action, "CONSCIOUSNESS");
                        q_table_.update(category, key, outcome.reward);
                        shared_.publish_report({"CONSCIOUSNESS", outcome.action, outcome.message,
                                                static_cast<std::size_t>(outcome.triples_added),
                                                static_cast<std::size_t>(outcome.contradictions_found),
                                                outcome.reward, now_epoch()});
                        break;
                    }
                }

                for (std::size_t i = 1; i < decision.candidate_topics.size(); ++i) {
                    enqueue_topic(decision.candidate_topics[i]);
                }
            }

            if (hunger.curiosity_hunger > 0.55) {
                hypothesis_generator_.generate(3);
            }

            run_limbic_consolidation(shared_.drain_new_facts());
            q_table_.save();

            const double elapsed_ms = std::chrono::duration<double, std::milli>(
                std::chrono::steady_clock::now() - tick_start).count();
            {
                std::lock_guard<std::mutex> lock(state_mutex_);
                autonomic_.last_tick_ms = elapsed_ms;
                if (elapsed_ms > 10000.0) {
                    autonomic_.slow_mode = true;
                    autonomic_.crawler_threads = SLOW_CRAWLER_THREADS;
                }
            }
            if (elapsed_ms > 4500.0) {
                Logger::console("TICK", "tick duration " + format_double(elapsed_ms, 2) + "ms", COLOR_YELLOW);
            }

            const auto tick_elapsed = std::chrono::steady_clock::now() - tick_start;
            if (tick_elapsed < CONSCIOUSNESS_TICK) {
                std::this_thread::sleep_for(CONSCIOUSNESS_TICK - tick_elapsed);
            }
        }
    }

    void explorer_loop() {
        while (running_.load()) {
            auto topic = dequeue_topic(std::chrono::milliseconds(1500));
            if (topic.has_value()) {
                const std::string category = omega_.topic_category(*topic);
                ActionOutcome outcome = execute_crawl(*topic, "EXPLORER");
                q_table_.update(category, "CRAWL:" + *topic, outcome.reward);
                shared_.publish_report({"EXPLORER", outcome.action, outcome.message,
                                        static_cast<std::size_t>(outcome.triples_added), 0,
                                        outcome.reward, now_epoch()});
                continue;
            }

            ActionOutcome verify = verify_oldest_hypothesis("EXPLORER");
            if (verify.ok) {
                shared_.publish_report({"EXPLORER", verify.action, verify.message, 0, 0,
                                        verify.reward, now_epoch()});
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(400));
        }
    }

    void optimizer_loop() {
        while (running_.load()) {
            std::this_thread::sleep_for(std::chrono::seconds(20));
            if (!running_.load()) {
                break;
            }
            ActionOutcome outcome = consolidate_memory();
            shared_.publish_report({"OPTIMIZER", outcome.action, outcome.message,
                                    0, 0, outcome.reward, now_epoch()});
        }
    }

    void safety_loop() {
        while (running_.load()) {
            std::this_thread::sleep_for(std::chrono::seconds(10));
            if (!running_.load()) {
                break;
            }
            ActionOutcome outcome = run_contradiction_sweep();
            shared_.publish_report({"SAFETY_CHECKER", outcome.action, outcome.message,
                                    0, static_cast<std::size_t>(outcome.contradictions_found),
                                    outcome.reward, now_epoch()});
        }
    }

    ROSHANReceptor receptor_;
    SymbolEncoder encoder_;
    KnowledgeMesh mesh_;
    OmegaMemory omega_;
    HypothesisStore hypotheses_;
    ParadoxStore paradoxes_;
    SharedMemory shared_;
    ActionValueEstimator q_table_;
    ContradictionDetector contradiction_detector_;
    FactVerifier verifier_;
    ReasoningCortex cortex_;
    MultiHopReasoner hop_reasoner_;
    Medulla medulla_;
    Hypothalamus hypothalamus_;
    LimbicSystem limbic_;
    WorldPlanner planner_;
    FrontalCortex frontal_;
    HypothesisGenerator hypothesis_generator_;

    // ── Context window ────────────────────────────────────────────────
    struct Turn {
        std::string user_input;
        std::string last_entity;  // main entity mentioned in that turn
    };
    std::deque<Turn> context_window_;   // last 5 turns
    static constexpr std::size_t CTX_MAX = 5;
    AnswerPlan last_answer_;
    std::deque<std::string> knowledge_gaps_;
    bool offline_only_{false};
    std::string response_mode_{"chat"};

    // ── Intent classifier ─────────────────────────────────────────────
    enum class Intent { GREETING, SELF_QUERY, OPINION, FACTUAL };

    static Intent classify_intent(const std::string& raw) {
        const std::string q = lower_copy(raw);

        // Greeting
        static const std::vector<std::string> greetings = {
            "hi","hello","hey","namaste","namaskar","hola","howdy",
            "good morning","good afternoon","good evening","good night",
            "sup","what's up","whats up","yo","greetings","salut","bonjour"
        };
        for (const auto& g : greetings) {
            if (q == g || q.find(g) == 0) return Intent::GREETING;
        }

        // Self-query (about the system itself)
        static const std::vector<std::string> self_tokens = {
            "who are you","what are you","tell me about yourself",
            "who am i","what am i","what can you do","your name",
            "introduce yourself","aap kaun ho","tum kaun ho","tu kaun hai"
        };
        for (const auto& s : self_tokens) {
            if (q.find(s) != std::string::npos) return Intent::SELF_QUERY;
        }

        // Opinion request — flag it; system stays neutral
        static const std::vector<std::string> opinion_tokens = {
            "is he good","is she good","is it good","is he bad","is she bad",
            "is he better","is she better","what do you think","your opinion",
            "do you like","do you prefer","best prime minister","worst",
            "rate him","rate her","judge him","should i","would you recommend",
            "kya aap sochte","tera opinion","acha hai ya bura","acha h ya bura",
            "good or bad","good or evil","better or worse","is he the best"
        };
        for (const auto& o : opinion_tokens) {
            if (q.find(o) != std::string::npos) return Intent::OPINION;
        }

        return Intent::FACTUAL;
    }

    // ── Pronoun resolver — uses context window ────────────────────────
    std::string resolve_pronouns(const std::string& raw) const {
        if (context_window_.empty()) return raw;
        const std::string& last_entity = context_window_.back().last_entity;
        if (last_entity.empty()) return raw;

        std::string resolved = raw;
        static const std::vector<std::string> pronouns = {
            "he ","she ","it ","they ","him ","her ","them ","this ","that ","these ","those "
        };
        const std::string ql = lower_copy(raw);
        for (const auto& p : pronouns) {
            const std::size_t pos = ql.find(p);
            if (pos != std::string::npos) {
                resolved = raw.substr(0, pos) + last_entity + " " + raw.substr(pos + p.size());
                break;
            }
        }
        return resolved;
    }

    // ── Extract dominant entity from question ─────────────────────────
    static std::string dominant_entity(const std::string& question,
                                       const std::vector<Entity>& entities) {
        if (!entities.empty()) return entities.front().text;
        // fallback: first capitalised word
        std::istringstream ss(question);
        std::string word;
        while (ss >> word) {
            if (!word.empty() && std::isupper(static_cast<unsigned char>(word[0])))
                return word;
        }
        return {};
    }

    mutable std::mutex state_mutex_;
    mutable std::mutex contradiction_mutex_;
    std::atomic<bool> running_{false};
    std::atomic<bool> dirty_state_{false};
    std::unordered_set<std::string> seen_contradictions_;
    AutonomicState autonomic_;
    HungerState last_hunger_;
    std::deque<std::string> topic_queue_;
    std::unordered_set<std::string> queued_topics_;
    std::condition_variable queue_cv_;
    std::mutex queue_mutex_;
    std::thread consciousness_thread_;
    std::thread explorer_thread_;
    std::thread optimizer_thread_;
    std::thread safety_thread_;
    std::chrono::steady_clock::time_point startup_time_{std::chrono::steady_clock::now()};
    mutable std::mt19937_64 rng_{std::random_device{}()};
};

}  // namespace infinity

namespace {

void signal_handler(int) {
    infinity::g_shutdown_requested.store(true);
}

std::vector<std::string> parse_two_fields(const std::string& rest) {
    std::vector<std::string> out;
    const std::size_t pipe = rest.find('|');
    if (pipe != std::string::npos) {
        out.push_back(infinity::trim_copy(rest.substr(0, pipe)));
        out.push_back(infinity::trim_copy(rest.substr(pipe + 1)));
        return out;
    }

    std::string current;
    bool in_quotes = false;
    for (char c : rest) {
        if (c == '"') {
            in_quotes = !in_quotes;
            if (!in_quotes && !current.empty()) {
                out.push_back(current);
                current.clear();
            }
            continue;
        }
        if (!in_quotes && std::isspace(static_cast<unsigned char>(c))) {
            if (!current.empty()) {
                out.push_back(current);
                current.clear();
            }
            continue;
        }
        current.push_back(c);
    }
    if (!current.empty()) {
        out.push_back(current);
    }
    for (std::string& part : out) {
        part = infinity::trim_copy(part);
    }
    return out;
}

}  // namespace

int main() {
    std::signal(SIGINT, signal_handler);
    std::signal(SIGTERM, signal_handler);

    // ── ASCII Banner ──────────────────────────────────────────────────
    std::cout << "\n"
        << "  \033[36m██ ███    ██ ███████ ██ ███    ██ ██ ████████ ██    ██\033[0m\n"
        << "  \033[36m██ ████   ██ ██      ██ ████   ██ ██    ██     ██  ██ \033[0m\n"
        << "  \033[36m██ ██ ██  ██ █████   ██ ██ ██  ██ ██    ██      ████  \033[0m\n"
        << "  \033[36m██ ██  ██ ██ ██      ██ ██  ██ ██ ██    ██       ██   \033[0m\n"
        << "  \033[36m██ ██   ████ ██      ██ ██   ████ ██    ██       ██   \033[0m\n"
        << "          \033[1;37m♾️   LIVING KNOWLEDGE ORGANISM v4.0\033[0m\n"
        << "    \033[33mIntent-aware | Context memory | Nishpaksh reasoning\033[0m\n\n";

    std::cout << "Enter passphrase: " << std::flush;
    std::string passphrase;
    std::getline(std::cin, passphrase);
    if (passphrase.empty()) {
        std::cerr << "Passphrase required.\n";
        return 1;
    }

    try {
        infinity::SovereignBrain brain(passphrase);
        brain.start();

        std::cout << "\n\033[1;37m♾️  INFINITY COMMANDS\033[0m\n"
            << "  \033[32mlearn\033[0m  <topic>    → Wikipedia se ek topic seekho\n"
            << "  \033[32mdeep\033[0m   <topic>    → Topic + saare subtopics (deep crawl)\n"
            << "  \033[32mbulk\033[0m              → 50 starter topics download karo\n"
            << "  \033[32mevolve\033[0m            → Auto-evolution on karo\n"
            << "  \033[32mpause\033[0m             → Evolution rok do\n"
            << "  \033[32mhypothesize\033[0m       → Nayi discoveries generate karo\n"
            << "  \033[32mstatus\033[0m            → Brain stats dekho\n"
            << "  \033[32magents\033[0m            → Agent swarm status\n"
            << "  \033[32mparadoxes\033[0m         → Unsolved contradictions dekho\n"
            << "  \033[32msemantic\033[0m <term>   → HDV nearest concepts dekho\n"
            << "  \033[32mhop\033[0m <A> <B>       → A se B tak reasoning chain\n"
            << "  \033[32mcontradictions\033[0m    → Known conflicts list karo\n"
            << "  \033[32msave / load\033[0m       → State persist karo\n"
            << "  \033[32mexit\033[0m              → Bahar jao\n"
            << "  \033[33m<koi bhi sawaal>\033[0m  → Seedha poochho — prefix nahi chahiye\n\n"
            << "\033[33mSpecial:\033[0m Context yaad rakhta hai (last 5 turns)\n"
            << "         Opinion sawaalon pe nishpaksh facts deta hai\n"
            << "         Greeting samajhta hai — Wikipedia nahi khodta\n\n";
        std::string line;
        while (!infinity::g_shutdown_requested.load()) {
            std::cout << "\033[36m♾️ >\033[0m " << std::flush;
            if (!std::getline(std::cin, line)) {
                break;
            }
            line = infinity::trim_copy(line);
            if (line.empty()) {
                continue;
            }

            std::istringstream iss(line);
            std::string cmd;
            iss >> cmd;
            std::string rest;
            std::getline(iss, rest);
            rest = infinity::trim_copy(rest);
            cmd = infinity::lower_copy(cmd);

            try {
                if (cmd == "quit" || cmd == "exit") {
                    break;
                }
                if (cmd == "help") {
                    std::cout
                        << "ask <question>\n"
                        << "learn <topic>\n"
                        << "hypothesize\n"
                        << "status\n"
                        << "agents\n"
                        << "paradoxes\n"
                        << "plan <goal_description>\n"
                        << "semantic <term>\n"
                        << "deduce <subject> <relation>\n"
                        << "hop <conceptA> <conceptB>\n"
                        << "contradictions\n"
                        << "import <path>\n"
                        << "why\n"
                        << "gaps\n"
                        << "offline on|off\n"
                        << "mode chat|agent|reason|mythos\n"
                        << "identity\n"
                        << "teach <subject>|<relation>|<object>\n"
                        << "recall <query>\n"
                        << "forgetgap <topic|all>\n"
                        << "export [file.tsv]\n"
                        << "selftest\n"
                        << "skills\n"
                        << "belief\n"
                        << "critic\n"
                        << "save [file]\n"
                        << "load [file]\n"
                        << "quit\n";
                    continue;
                }
                if (cmd == "ask") {
                    std::cout << brain.answer_question(rest) << "\n";
                    continue;
                }
                if (cmd == "learn") {
                    std::cout << brain.learn_topic(rest) << "\n";
                    continue;
                }
                if (cmd == "hypothesize") {
                    std::cout << brain.run_hypothesis_cycle() << "\n";
                    continue;
                }
                if (cmd == "status") {
                    std::cout << brain.status_string() << "\n";
                    continue;
                }
                if (cmd == "agents") {
                    std::cout << brain.agents_string() << "\n";
                    continue;
                }
                if (cmd == "paradoxes") {
                    std::cout << brain.paradoxes_string() << "\n";
                    continue;
                }
                if (cmd == "plan") {
                    std::cout << brain.plan_and_execute(rest) << "\n";
                    continue;
                }
                if (cmd == "semantic") {
                    std::cout << brain.semantic_string(rest) << "\n";
                    continue;
                }
                if (cmd == "deduce") {
                    auto parts = parse_two_fields(rest);
                    if (parts.size() > 2) {
                        const std::string relation = parts.back();
                        parts.pop_back();
                        parts = {infinity::join_strings(parts, " "), relation};
                    }
                    if (parts.size() < 2) {
                        std::cout << "Usage: deduce <subject> <relation>  (quote multi-word subjects)\n";
                    } else {
                        std::cout << brain.deduce_string(parts[0], parts[1]) << "\n";
                    }
                    continue;
                }
                if (cmd == "hop") {
                    const auto parts = parse_two_fields(rest);
                    if (parts.size() != 2) {
                        std::cout << "Usage: hop <conceptA> <conceptB>  (quote multi-word concepts or use A | B)\n";
                    } else {
                        std::cout << brain.hop_string(parts[0], parts[1]) << "\n";
                    }
                    continue;
                }
                if (cmd == "contradictions") {
                    std::cout << brain.contradictions_string() << "\n";
                    continue;
                }
                if (cmd == "import") {
                    std::cout << brain.import_path(rest) << "\n";
                    continue;
                }
                if (cmd == "why") {
                    std::cout << brain.why_string() << "\n";
                    continue;
                }
                if (cmd == "gaps") {
                    std::cout << brain.gaps_string() << "\n";
                    continue;
                }
                if (cmd == "offline") {
                    std::cout << brain.set_offline_mode(rest) << "\n";
                    continue;
                }
                if (cmd == "mode") {
                    std::cout << brain.set_response_mode(rest) << "\n";
                    continue;
                }
                if (cmd == "identity") {
                    std::cout << brain.identity_string() << "\n";
                    continue;
                }
                if (cmd == "teach") {
                    std::cout << brain.teach_fact(rest) << "\n";
                    continue;
                }
                if (cmd == "recall") {
                    std::cout << brain.recall_memory(rest) << "\n";
                    continue;
                }
                if (cmd == "forgetgap") {
                    std::cout << brain.forget_gap(rest) << "\n";
                    continue;
                }
                if (cmd == "export") {
                    std::cout << brain.export_knowledge(rest) << "\n";
                    continue;
                }
                if (cmd == "selftest") {
                    std::cout << brain.self_test_string() << "\n";
                    continue;
                }
                if (cmd == "skills") {
                    std::cout << brain.skills_string() << "\n";
                    continue;
                }
                if (cmd == "belief") {
                    std::cout << brain.belief_string() << "\n";
                    continue;
                }
                if (cmd == "critic") {
                    std::cout << brain.critic_string() << "\n";
                    continue;
                }
                if (cmd == "save") {
                    const std::string path = rest.empty() ? "infinity_state.snapshot" : rest;
                    std::cout << (brain.save_snapshot(path) ? "Saved.\n" : "Save failed.\n");
                    continue;
                }
                if (cmd == "load") {
                    const std::string path = rest.empty() ? "infinity_state.snapshot" : rest;
                    std::cout << (brain.load_snapshot(path) ? "Loaded.\n" : "Load failed.\n");
                    continue;
                }

                // Treat as direct question — pass full line
                std::cout << brain.answer_question(line) << "\n";
            } catch (const std::exception& ex) {
                std::cout << "Command failed: " << ex.what() << "\n";
            }
        }

        brain.stop();
        return 0;
    } catch (const std::exception& ex) {
        std::cerr << "INFINITY startup/runtime failure: " << ex.what() << "\n";
        return 1;
    }
}
