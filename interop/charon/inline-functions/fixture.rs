// The selected helper must preserve mutation, early return and overflow abort.
#[inline(never)]
fn adjust(slot: &mut u32, increment: u32) -> Result<u32, ()> {
    if increment == 0 {
        return Err(());
    }
    let previous = *slot;
    *slot = previous + increment;
    Ok(previous)
}

pub fn twice(slot: &mut u32, left: u32, right: u32) -> Result<(u32, u32), ()> {
    let first = adjust(slot, left)?;
    let second = adjust(slot, right)?;
    Ok((first, second))
}

// This is the hidden shared-region shape used by the constructor's closures.
pub fn capture(value: Option<usize>, factor: &usize) -> Option<usize> {
    value.and_then(|n| n.checked_mul(*factor))
}
