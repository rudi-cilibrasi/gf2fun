// Binary fields, Frobenius orbits and norm fibres for the auxiliary circle calculations.
#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

using Word = std::uint32_t;

struct Field {
    const unsigned m, q, size, period;
    std::vector<Word> exp, log, conjugate, real, real_index, representatives, masks;
    std::vector<Word> orbit_id, degree, to_rep;
    std::vector<std::vector<Word>> norm_fibres;

    static unsigned extension_degree(unsigned base) {
        switch (base) {
            case 512: return 18;
            case 1024: return 20;
            case 2048: return 22;
            default: throw std::invalid_argument("unsupported binary circle field");
        }
    }

    explicit Field(unsigned base) :
        m(extension_degree(base)), q(base), size(q*q), period(size-1),
        exp(2*period), log(size, size), conjugate(size), real_index(size, size),
        orbit_id(size, size), degree(size), to_rep(size), norm_fibres(q) {
        const Word modulus = m == 18 ? 0x41403 : (m == 20 ? 0x100009 : 0x400003);
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
            std::array<Word, 23> poly{};
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
