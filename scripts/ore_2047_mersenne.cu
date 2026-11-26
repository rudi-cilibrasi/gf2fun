// One field residue occupies 63 radix-2^32 words and one 31-bit top word.
// The host checks signed accumulator bounds before launching a matrix product.
using Word = unsigned int;
using U64 = unsigned long long;
using I64 = long long;

__device__ void normalize(I64 *digits) {
    I64 carry = 0;
    for (int i = 0; i < 63; ++i) {
        I64 value = digits[i] + carry;
        digits[i] = static_cast<Word>(value);
        carry = value >> 32;
    }
    I64 top = digits[63] + carry;
    digits[63] = static_cast<Word>(top) & 0x7fffffffU;
    carry = top >> 31;
    // 2^2047 is one modulo the group order. This also handles negative carries.
    while (carry) {
        for (int i = 0; i < 64 && carry; ++i) {
            I64 value = digits[i] + carry;
            digits[i] = static_cast<Word>(value) & (i == 63 ? 0x7fffffffU : 0xffffffffU);
            carry = value >> (i == 63 ? 31 : 32);
        }
    }
}

extern "C" __global__ void spmv(const Word *ptr, const Word *entries, const Word *diagonal,
                                const Word *x, Word *y, int n,
                                const Word *coefficients, int add_index) {
    int lane = threadIdx.x & 31, warp = threadIdx.x >> 5;
    int row = (blockIdx.x * blockDim.x + threadIdx.x) >> 5;
    if (row >= n) return;
    I64 low = 0, high = 0;
    unsigned end = ptr[row+1];
    for (unsigned j = ptr[row]; j < end; j += 32) {
        Word item = j+lane < end ? entries[j+lane] : 0;
        unsigned count = min(end-j, 32U);
        for (unsigned k = 0; k < count; ++k) {
            Word entry = __shfl_sync(0xffffffff, item, k);
            const Word *value = x + 64*(entry & 65535);
            int scale = static_cast<short>(entry >> 16);
            if (scale == 1) {
                low += value[lane];
                high += value[lane+32];
            } else {
                low += static_cast<I64>(scale)*value[lane];
                high += static_cast<I64>(scale)*value[lane+32];
            }
        }
    }
    __shared__ I64 memory[4][64];
    I64 *digits = memory[warp];
    digits[lane] = low*diagonal[row];
    digits[lane+32] = high*diagonal[row];
    if (row == n-1 && add_index >= 0) {
        const Word *add = coefficients + 64*add_index;
        digits[lane] += add[lane];
        digits[lane+32] += add[lane+32];
    }
    __syncwarp();
    if (lane == 0) normalize(digits);
    __syncwarp();
    y[64*row+lane] = static_cast<Word>(digits[lane]);
    y[64*row+lane+32] = static_cast<Word>(digits[lane+32]);
}

extern "C" __global__ void partial(const Word *x, const Word *u, U64 *out, int n) {
    int group = threadIdx.x >> 6, limb = threadIdx.x & 63;
    int start = blockIdx.x*128;
    U64 value = 0;
    for (int j = start+group; j < min(n, start+128); j += 4)
        value += static_cast<U64>(x[64*j+limb])*u[j];
    __shared__ U64 sums[4][64];
    sums[group][limb] = value;
    __syncthreads();
    if (group == 0)
        out[64*blockIdx.x+limb] = sums[0][limb]+sums[1][limb]+sums[2][limb]+sums[3][limb];
}

extern "C" __global__ void finish(const U64 *partial_sums, Word *sequence, int blocks, int k) {
    int limb = threadIdx.x;
    U64 sum = 0;
    for (int j = 0; j < blocks; ++j) sum += partial_sums[64*j+limb];
    __shared__ I64 digits[64];
    digits[limb] = static_cast<I64>(sum);
    __syncthreads();
    if (limb == 0) normalize(digits);
    __syncthreads();
    sequence[k*64+limb] = static_cast<Word>(digits[limb]);
}
