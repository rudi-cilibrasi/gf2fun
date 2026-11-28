// One modular squaring per launch in GF(2)[X]/(X^n + X^c + X^b + X^a + 1).
// Each input row has three extra zero words for unaligned reads at its high end.
using Word = unsigned int;

__device__ __forceinline__ Word spread_even_bits(Word value) {
    value = (value | (value << 8)) & 0x00ff00ffu;
    value = (value | (value << 4)) & 0x0f0f0f0fu;
    value = (value | (value << 2)) & 0x33333333u;
    return (value | (value << 1)) & 0x55555555u;
}

// The 32 bits starting at position pos in the unreduced square.
// Only 16 successive input bits contribute because squaring doubles exponents.
__device__ __forceinline__ Word square_window(const Word *input, int pos) {
    const int start = (pos + 1) / 2;
    const int index = start / 32;
    Word bits = __funnelshift_r(input[index], input[index + 1], start % 32);
    return spread_even_bits(bits & 0xffffu) << (pos % 2);
}

__device__ __forceinline__ Word low_mask(int count) {
    if (count <= 0) return 0;
    return count >= 32 ? ~0u : (1u << count) - 1;
}

// A window in floor(square/X^n), treating negative coefficient indices as zero.
__device__ __forceinline__ Word high_window(const Word *input, int n, int pos) {
    if (pos <= -32 || pos >= n) return 0;
    if (pos < 0) return square_window(input, n) << (-pos);
    return square_window(input, n + pos);
}

__device__ __forceinline__ Word first_fold(const Word *input, int n, int pos, int a, int b, int c) {
    Word low = pos < n ? square_window(input, pos) & low_mask(n - pos) : 0;
    return low ^ high_window(input, n, pos) ^ high_window(input, n, pos - a)
               ^ high_window(input, n, pos - b) ^ high_window(input, n, pos - c);
}

// The first fold can reach degree n+c-2. Only the lowest 2c-1 output bits
// can receive a contribution when the surplus is folded a second time.
__device__ __forceinline__ Word surplus(const Word *input, int n, int pos, int a, int b, int c) {
    if (pos <= -32 || pos >= c) return 0;
    if (pos < 0) return first_fold(input, n, n, a, b, c) << (-pos);
    return first_fold(input, n, n + pos, a, b, c);
}

extern "C" __global__ void square_mod(Word *output, const Word *input, const int *taps,
                                     int n, int words) {
    const int index = blockIdx.x * blockDim.x + threadIdx.x;
    if (index >= words) return;
    const int row = blockIdx.y;
    const auto offset = static_cast<unsigned long long>(row) * (words + 3);
    const Word *source = input + offset;
    const int a = taps[3 * row], b = taps[3 * row + 1], c = taps[3 * row + 2];
    const int pos = 32 * index;
    Word value = first_fold(source, n, pos, a, b, c);
    if (pos < 2 * c) {
        value ^= surplus(source, n, pos, a, b, c) ^ surplus(source, n, pos - a, a, b, c)
               ^ surplus(source, n, pos - b, a, b, c) ^ surplus(source, n, pos - c, a, b, c);
    }
    output[offset + index] = value & low_mask(n - pos);
}
