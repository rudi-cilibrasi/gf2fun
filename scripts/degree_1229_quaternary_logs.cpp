// Verify projected quaternary norm logarithms in the absolute binary field of degree 2458.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <array>
#include <iostream>
#include <stdexcept>
#include <vector>

using NTL::GF2X;
using NTL::GF2XModulus;
using NTL::ZZ;

namespace {
constexpr int n = 1229, size = 1 << 18, constant_modulus = 0x41403;
constexpr int window = 6;
using Powers = std::vector<std::array<GF2X, 1 << window>>;

GF2X binary(const ZZ& mask) {
    std::vector<unsigned char> bytes(NTL::NumBytes(mask));
    NTL::BytesFromZZ(bytes.data(), mask, bytes.size());
    return NTL::GF2XFromBytes(bytes.data(), bytes.size());
}

class ConstantField {
    std::vector<int> powers, logs;
public:
    int omega;
    ConstantField() : powers(2*size), logs(size, -1) {
        int x = 1;
        for (int i = 0; i < size-1; ++i) {
            if (logs[x] >= 0) throw std::logic_error("short constant orbit");
            powers[i] = powers[i+size-1] = x;
            logs[x] = i;
            x <<= 1;
            if (x & size) x ^= constant_modulus;
        }
        if (x != 1) throw std::logic_error("incorrect constant modulus");
        omega = powers[(size-1)/3];
    }
    int mul(int a, int b) const { return a && b ? powers[logs[a]+logs[b]] : 0; }
    int fourth(int x) const { return mul(mul(x,x),mul(x,x)); }

    std::vector<int> minimal(int t) const {
        std::vector<int> p{1};
        int v = t;
        do {
            if (v < t) throw std::logic_error("label is not the minimum in its F_4 orbit");
            p.push_back(0);
            for (int j = static_cast<int>(p.size())-1; j > 0; --j)
                p[j] = p[j-1] ^ mul(p[j],v);
            p[0] = mul(p[0],v);
            v = fourth(v);
        } while (v != t);
        for (int& c : p) {
            if (c == omega) c = 2;
            else if (c == (omega^1)) c = 3;
            else if (c > 1) throw std::logic_error("coefficient outside F_4");
        }
        return p;
    }
};

Powers powers_of(GF2X base, const ZZ& order, const GF2XModulus& field) {
    Powers powers((NTL::NumBits(order)+window-1)/window);
    for (auto& column : powers) {
        NTL::set(column[0]);
        for (size_t d=1; d<column.size(); ++d)
            NTL::MulMod(column[d], column[d-1], base, field);
        NTL::MulMod(base, column.back(), base, field);
    }
    return powers;
}

GF2X evaluate_power(const Powers& powers, const ZZ& e, const GF2XModulus& field) {
    GF2X r(1);
    long offset = 0;
    for (const auto& column : powers) {
        int digit = 0;
        for (int i=0; i<window; ++i) digit |= NTL::bit(e,offset+i) << i;
        if (digit) NTL::MulMod(r,r,column[digit],field);
        offset += window;
    }
    return r;
}
}

int main() {
    ZZ modulus, z_mask, known, cofactor;
    if (!(std::cin >> modulus >> z_mask >> known >> cofactor)) return 1;
    const GF2X f = binary(modulus), z = binary(z_mask);
    const GF2XModulus field(f);
    if (NTL::deg(f) != 2*n || !NTL::IterIrredTest(f) ||
        !NTL::IsOne(NTL::SqrMod(z,field)+z) || known*cofactor != NTL::power2_ZZ(n)-1) return 1;
    const GF2X x(1,1);
    const GF2X conjugate_x = NTL::PowerXMod(NTL::power2_ZZ(n),field);
    const GF2X conjugate_z = z+1;
    std::array<std::array<GF2X,4>,10> direct{}, conjugate{};
    GF2X a(1), b(1);
    for (int i=0; i<=9; ++i) {
        direct[i][1]=a;
        direct[i][2]=NTL::MulMod(a,z,field);
        direct[i][3]=direct[i][2]+a;
        conjugate[i][1]=b;
        conjugate[i][2]=NTL::MulMod(b,conjugate_z,field);
        conjugate[i][3]=conjugate[i][2]+b;
        NTL::MulByXMod(a,a,field);
        NTL::MulMod(b,b,conjugate_x,field);
    }
    const GF2X anchor = NTL::PowerMod(NTL::MulMod(x,conjugate_x,field),9,field);
    const GF2X projected = NTL::PowerMod(anchor,known,field);
    if (NTL::IsOne(projected) || !NTL::IsOne(NTL::PowerMod(projected,cofactor,field))) return 1;
    const Powers powers = powers_of(projected,cofactor,field);
    const ConstantField constants;
    std::vector<std::pair<int,ZZ>> rows;
    int mask;
    ZZ log;
    while (std::cin >> mask) {
        if (mask < 0 || mask >= size || !(std::cin >> log) || log < 0 || log >= cofactor) return 1;
        rows.emplace_back(mask,log);
    }
    if (!std::cin.eof() || rows.empty()) return 1;
    bool valid = true;
    #pragma omp parallel reduction(&&:valid)
    {
        const GF2XModulus local(f);
        #pragma omp for schedule(static)
        for (size_t i=0; i<rows.size(); ++i) {
            const auto poly = constants.minimal(rows[i].first);
            const long d = static_cast<long>(poly.size())-1;
            if (9 % d) { valid = false; continue; }
            GF2X v, w;
            for (long j=0; j<=d; ++j) {
                v += direct[j][poly[j]];
                w += conjugate[j][poly[j]];
            }
            const GF2X norm = NTL::MulMod(v,w,local);
            if (NTL::PowerMod(norm,known*(9/d),local) != evaluate_power(powers,rows[i].second,local))
                valid = false;
        }
    }
    if (!valid) {
        std::cerr << "A full-field projected norm identity failed.\n";
        return 1;
    }
    std::cout << "Direct binary powering verified " << rows.size() << " projected norm identities.\n";
}
