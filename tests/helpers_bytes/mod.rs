//! Byte key sampler shared by the property tests.

pub fn sample_byte_key(ctx: &mut noprop::TestCaseContext) -> Vec<u8> {
    let len = noprop::sample_with_boundaries(
        ctx,
        &[0usize, 1, 2, 8],
        noprop::Ratio::one_nth(8),
        |_ctx| noprop::sample_usize_in(_ctx, 0..=16),
    );
    let mut key = Vec::with_capacity(len);
    for _ in 0..len {
        if noprop::sample_ratio(ctx, noprop::Ratio::one_nth(2)) {
            key.push(noprop::sample_u8(ctx));
        } else {
            key.push(b"abc"[noprop::sample_usize_in(ctx, 0..3)]);
        }
    }
    key
}
