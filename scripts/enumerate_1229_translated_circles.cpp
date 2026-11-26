// Enumerate Frobenius orbits of translated norm circles whose sextic splits.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr int q = 1024;
constexpr int field_size = q * q;
constexpr int group_order = field_size - 1;
constexpr int field_modulus = (1 << 20) | (1 << 3) | 1;

struct Field {
    std::vector<int> power = std::vector<int>(2 * group_order);
    std::vector<int> logarithm = std::vector<int>(field_size, -1);
    std::vector<int> conjugate = std::vector<int>(field_size);
    std::vector<int> orbit_id = std::vector<int>(field_size, -1);
    std::vector<int> representatives;
    std::vector<std::uint8_t> degree = std::vector<std::uint8_t>(field_size);
    std::vector<std::uint8_t> to_representative = std::vector<std::uint8_t>(field_size);
    std::array<std::array<int, q - 1>, 20> radius_exponents{};

    int multiply(int a, int b) const {
        return a && b ? power[logarithm[a] + logarithm[b]] : 0;
    }

    int inverse(int a) const {
        if (!a) throw std::runtime_error("zero inverse");
        return power[group_order - logarithm[a]];
    }

    Field() {
        int x = 1;
        for (int i = 0; i < group_order; ++i) {
            if (logarithm[x] >= 0) throw std::runtime_error("short generator period");
            power[i] = power[group_order + i] = x;
            logarithm[x] = i;
            x <<= 1;
            if (x & field_size) x ^= field_modulus;
        }
        if (x != 1) throw std::runtime_error("incorrect generator period");
        for (int i = 1; i < field_size; ++i) {
            auto exponent = static_cast<std::int64_t>(logarithm[i]) * q;
            conjugate[i] = power[exponent % group_order];
        }
        for (int r = 0; r < q - 1; ++r) {
            int exponent = r;
            for (auto& conjugates : radius_exponents) {
                conjugates[r] = exponent;
                exponent = 2 * exponent % (q - 1);
            }
        }
        for (int c = 0; c < field_size; ++c) {
            if (orbit_id[c] >= 0) continue;
            int id = representatives.size();
            representatives.push_back(c);
            int length = 0;
            int value = c;
            do {
                orbit_id[value] = id;
                to_representative[value] = length++;
                value = multiply(value, value);
            } while (value != c);
            do {
                degree[value] = length;
                to_representative[value] = (length - to_representative[value]) % length;
                value = multiply(value, value);
            } while (value != c);
        }
    }
};

struct Circle {
    int center, radius;
    std::array<int, 6> roots{};
    unsigned root_count = 0;
};

template <typename Record>
void enumerate_roots(const Field& field, Record record) {
    int theta = 0;
    while ((theta ^ field.conjugate[theta]) != 1) ++theta;
    for (int a : field.representatives) {
        int a2 = field.multiply(a, a);
        int a3 = field.multiply(a2, a);
        int h1 = a3 ^ a;
        if (!h1) {
            // At a pole a = 0 or 1 the sextic vanishes exactly for center a.
            for (int r = 0; r < q - 1; ++r) record(field.orbit_id[a] * (q - 1) + r, a);
            continue;
        }
        int h0 = field.multiply(a2, a3) ^ a2 ^ 1;
        int t = field.multiply(h0, field.inverse(h1));
        int direction = a ^ field.conjugate[t];
        std::array<int, 20> conjugates{a};
        for (int j = 1; j < field.degree[a]; ++j)
            conjugates[j] = field.multiply(conjugates[j - 1], conjugates[j - 1]);

        // Enumerate conjugates of a exactly once, retaining canonical centers.
        auto visit = [&](int b) {
            int rho = field.multiply(t ^ b, a ^ field.conjugate[b]);
            if (!rho) return;
            int exponent = field.logarithm[rho];
            if (exponent % (q + 1)) throw std::runtime_error("radius outside the base field");
            int r = exponent / (q + 1);
            int offset = field.orbit_id[b] * (q - 1);
            for (int j = field.to_representative[b]; j < field.degree[a]; j += field.degree[b])
                record(offset + field.radius_exponents[j][r], conjugates[j]);
        };
        if (!direction) {
            // Every center makes the radius a base-field element.
            for (int b = 0; b < field_size; ++b) visit(b);
        } else {
            // Tr(b * direction) = Tr(t * a) gives an affine line of centers.
            int ta = field.multiply(t, a);
            int trace = ta ^ field.conjugate[ta];
            int inv = field.inverse(direction);
            int base = field.multiply(field.multiply(theta, trace), inv);
            visit(base);
            for (int j = 0; j < q - 1; ++j)
                visit(base ^ field.power[field.logarithm[inv] + (q + 1) * j]);
        }
    }
}

void print_circle(Circle& circle, const Field& field) {
    std::sort(circle.roots.begin(), circle.roots.end());
    if (circle.root_count != 6 ||
        std::adjacent_find(circle.roots.begin(), circle.roots.end()) != circle.roots.end())
        throw std::runtime_error("incorrect root list");
    std::cout << circle.center << ',' << circle.radius;
    for (int a : circle.roots) {
        int a2 = field.multiply(a, a), a3 = field.multiply(a2, a);
        int h1 = a3 ^ a, h0 = field.multiply(a2, a3) ^ a2 ^ 1;
        int value = field.multiply(h0 ^ field.multiply(circle.center, h1),
                                   a ^ field.conjugate[circle.center]);
        if (value != field.multiply(circle.radius, h1))
            throw std::runtime_error("sextic evaluation failed");
        std::cout << ',' << a;
    }
    std::cout << '\n';
}
}

int main(int argc, char** argv) {
    bool emit = argc == 2 && std::string(argv[1]) == "--csv";
    if (argc != 1 && !emit) {
        std::cerr << "usage: enumerate_1229_translated_circles [--csv]\n";
        return 2;
    }
    const Field field;
    std::vector<std::uint8_t> counts(field.representatives.size() * (q - 1));
    enumerate_roots(field, [&](int key, int) {
        if (++counts[key] > 6) throw std::runtime_error("more than six distinct roots");
    });

    std::array<int, 7> histogram{};
    std::vector<int> split_index;
    std::vector<Circle> splits;
    if (emit) split_index.assign(counts.size(), -1);
    for (int b : field.representatives) {
        int offset = field.orbit_id[b] * (q - 1);
        for (int r = 0; r < q - 1; ++r) {
            bool canonical = true;
            for (int j = field.degree[b]; j < 20; j += field.degree[b])
                if (field.radius_exponents[j][r] < r) canonical = false;
            if (!canonical) continue;
            int roots = counts[offset + r];
            ++histogram[roots];
            if (roots == 6 && emit) {
                split_index[offset + r] = splits.size();
                splits.push_back({b, field.power[(q + 1) * r]});
            }
        }
    }
    const std::array<int, 7> expected{19363739, 19661762, 10268154, 3117528, 1182986, 73, 92910};
    if (histogram != expected || field.representatives.size() != 52488)
        throw std::runtime_error("unexpected root census");
    if (emit) {
        enumerate_roots(field, [&](int key, int a) {
            int i = split_index[key];
            if (i >= 0) {
                auto& circle = splits[i];
                circle.roots.at(circle.root_count++) = a;
            }
        });
        std::cout << "center,norm_radius,root0,root1,root2,root3,root4,root5\n";
        for (auto& circle : splits) print_circle(circle, field);
    } else {
        std::cout << "distinct_roots,parameter_orbits\n";
        for (int i = 0; i <= 6; ++i) std::cout << i << ',' << histogram[i] << '\n';
    }
}
