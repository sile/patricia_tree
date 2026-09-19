//! String key sampler shared by the map and split property tests.

fn sample_char(ctx: &mut noprop::TestCaseContext) -> char {
    if noprop::sample_ratio(ctx, noprop::Ratio::one_nth(4)) {
        noprop::sample_char(ctx)
    } else {
        const CHARS: [char; 8] = ['a', 'b', 'z', '0', '-', 'é', '日', '🌏'];
        CHARS[noprop::sample_usize_in(ctx, 0..CHARS.len())]
    }
}

pub fn sample_string_key(ctx: &mut noprop::TestCaseContext) -> String {
    let len = noprop::sample_with_boundaries(
        ctx,
        &[0usize, 1, 2, 8],
        noprop::Ratio::one_nth(8),
        |_ctx| noprop::sample_usize_in(_ctx, 0..=12),
    );
    (0..len).map(|_| sample_char(ctx)).collect()
}
