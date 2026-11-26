// Enumerate splitting norm circles for the root of T^2047 + T^511 + 1.
// Build with c++ -O3 -std=c++17. The output is little-endian and deterministic.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint32_t;

struct Field {
    const unsigned m, q, size, period;
    std::vector<Word> exp, log, conjugate, real, real_index, representatives, masks;
    std::vector<Word> orbit_id, degree, to_rep;
    std::vector<std::vector<Word>> norm_fibres;

    explicit Field(unsigned base) :
        m(base == 512 ? 18 : 20), q(base), size(q*q), period(size-1),
        exp(2*period), log(size, size), conjugate(size), real_index(size, size),
        orbit_id(size, size), degree(size), to_rep(size), norm_fibres(q) {
        const Word modulus = m == 18 ? 0x41403 : 0x100009;
        Word x = 1;
        for (unsigned i = 0; i < period; ++i) {
            if (log[x] != size) throw std::runtime_error("short generator period");
            exp[i] = exp[i+period] = x;
            log[x] = i;
            x <<= 1;
            if (x & size) x ^= modulus;
        }
        if (x != 1) throw std::runtime_error("invalid field generator");
        for (Word a = 0; a < size; ++a) {
            conjugate[a] = frobenius(a, m/2);
            if (conjugate[a] == a) {
                real_index[a] = real.size();
                real.push_back(a);
            }
        }
        if (real.size() != q) throw std::runtime_error("incorrect subfield");
        for (Word a = 1; a < size; ++a)
            norm_fibres.at(real_index.at(mul(a, conjugate[a]))).push_back(a);
        for (unsigned i = 1; i < q; ++i)
            if (norm_fibres[i].size() != q+1) throw std::runtime_error("incorrect norm fibre");

        for (Word a = 0; a < size; ++a) {
            if (orbit_id[a] != size) continue;
            Word id = representatives.size();
            representatives.push_back(a);
            std::vector<Word> roots;
            std::array<Word, 21> poly{};
            poly[0] = 1;
            Word v = a;
            do {
                orbit_id[v] = id;
                int d = roots.size();
                for (int i = d; i >= 0; --i) {
                    poly[i+1] ^= poly[i];
                    poly[i] = mul(poly[i], v);
                }
                roots.push_back(v);
                v = frobenius(v, 1);
            } while (v != a);
            Word mask = 0;
            for (unsigned k = 0; k <= roots.size(); ++k) {
                if (poly[k] > 1) throw std::runtime_error("nonbinary minimal polynomial");
                mask |= poly[k] << k;
            }
            masks.push_back(mask);
            for (unsigned j = 0; j < roots.size(); ++j) {
                degree[roots[j]] = roots.size();
                to_rep[roots[j]] = (roots.size()-j) % roots.size();
            }
        }
    }

    Word mul(Word a, Word b) const { return a && b ? exp[log[a]+log[b]] : 0; }
    Word frobenius(Word a, unsigned j) const {
        return a ? exp[(std::uint64_t(log[a]) << j) % period] : 0;
    }
};

// Visit every distinct root z of G for every canonical centre b and real d.
// Each binary orbit of z is handled once. The possible centres at a fixed z
// are a subfield line, so enumeration takes O(q^3/m) field operations.
template<class Visit> void incidences(const Field& f, Visit visit) {
    for (Word b : f.representatives)
        if (b) visit(f.orbit_id[b]*f.q, 0);
    for (Word z : f.representatives) {
        if (!z) continue;
        Word x = f.frobenius(z, 2) ^ z;
        Word y = f.q == 512 ? z : f.frobenius(z, 1);
        Word h = y ^ f.conjugate[x], xy = f.mul(x, y);
        if (!h) throw std::runtime_error("unexpected nonzero exceptional root");
        Word inv = f.exp[f.period-f.log[h]];
        for (Word u : f.real) {
            Word b = f.mul(xy ^ u, inv);
            unsigned j = f.to_rep[b];
            if (j >= f.degree[z]) continue;
            Word d = xy ^ f.mul(b, y) ^ f.mul(f.conjugate[b], x);
            if (d == f.mul(b, f.conjugate[b])) continue;
            for (; j < f.degree[z]; j += f.degree[b]) {
                Word ri = f.real_index[f.frobenius(d, j)];
                if (ri >= f.q) throw std::runtime_error("pencil value outside subfield");
                visit(f.orbit_id[b]*f.q + ri, f.frobenius(z, j));
            }
        }
    }
}

void append(std::vector<char>& out, Word n, unsigned bytes) {
    for (unsigned k = 0; k < bytes; ++k) out.push_back(static_cast<char>(n >> (8*k)));
}

void generate(const Field& f, std::ostream& out) {
    const unsigned gdeg = f.q == 512 ? 5 : 6;
    const Word n = f.masks.size();
    std::vector<std::uint8_t> counts(n*f.q, 0);
    incidences(f, [&](Word i, Word) {
        if (++counts[i] > gdeg) throw std::runtime_error("too many roots");
    });
    const Word missing = std::numeric_limits<Word>::max();
    std::vector<Word> slots(counts.size(), missing);
    Word rows = 0;
    for (Word i = 0; i < counts.size(); ++i)
        if (counts[i] == gdeg) slots[i] = rows++;
    std::vector<std::array<Word,6>> roots(rows);
    std::fill(counts.begin(), counts.end(), 0);
    incidences(f, [&](Word i, Word z) {
        if (slots[i] != missing) roots[slots[i]].at(counts[i]++) = z;
    });

    std::vector<char> buf;
    append(buf, n, 4);
    append(buf, rows, 4);
    for (Word mask : f.masks) append(buf, mask, 4);
    out.write(buf.data(), buf.size());
    std::vector<int> coefficients(n);
    std::vector<unsigned> touched;
    for (Word i = 0; i < slots.size(); ++i) {
        if (slots[i] == missing) continue;
        Word b = f.representatives[i/f.q], d = f.real[i%f.q];
        Word c = f.mul(b, f.conjugate[b]) ^ d;
        auto add = [&](Word z, int scale) {
            Word id = f.orbit_id[z];
            touched.push_back(id);
            coefficients[id] += scale * int(f.m / f.degree[z]);
        };
        for (Word u : f.norm_fibres.at(f.real_index[c])) add(b ^ u, 1);
        // Confirm the residual root evaluations independently of the pencil formula.
        for (unsigned j = 0; j < gdeg; ++j) {
            Word z = roots[slots[i]][j], x = f.frobenius(z, 2) ^ z;
            Word y = f.q == 512 ? z : f.frobenius(z, 1);
            if ((f.mul(x ^ b, y ^ f.conjugate[b]) ^ c) != 0)
                throw std::runtime_error("incorrect residual root");
            for (unsigned k = 0; k < j; ++k)
                if (roots[slots[i]][k] == z) throw std::runtime_error("duplicate residual root");
            add(z, -512);
        }
        std::sort(touched.begin(), touched.end());
        touched.erase(std::unique(touched.begin(), touched.end()), touched.end());
        buf.clear();
        unsigned terms = 0;
        for (Word id : touched) terms += coefficients[id] != 0;
        append(buf, terms, 2);
        for (Word id : touched) {
            if (coefficients[id]) {
                append(buf, id, 2);
                append(buf, static_cast<Word>(coefficients[id]), 4);
                coefficients[id] = 0;
            }
        }
        out.write(buf.data(), buf.size());
        touched.clear();
    }
    if (!out) throw std::runtime_error("failed to write relations");
    std::cout << "q=" << f.q << ": " << n << " columns, " << rows << " splitting circles\n";
}

int main(int argc, char** argv) {
    if (argc != 3 || (std::string(argv[1]) != "512" && std::string(argv[1]) != "1024")) {
        std::cerr << "Usage: gen_2047_ore_circles {512|1024} output.bin\n";
        return 2;
    }
    try {
        std::ofstream out(argv[2], std::ios::binary);
        if (!out) throw std::runtime_error("cannot open output");
        generate(Field(std::stoul(argv[1])), out);
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
