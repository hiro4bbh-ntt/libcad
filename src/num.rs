//! The `std::num`-related utility.

/// Returns the number `n` logically shifted by `shift`.
/// ```rust
/// use libcad::num::bitlsh;
/// assert_eq!(0x20, bitlsh(0x10, 1));
/// assert_eq!(0x10, bitlsh(0x10, 0));
/// assert_eq!(0x08, bitlsh(0x10, -1));
/// ```
pub fn bitlsh(n: u64, shift: i64) -> u64 {
    if shift < 0 {
        return n >> (-shift);
    }
    n << shift
}
