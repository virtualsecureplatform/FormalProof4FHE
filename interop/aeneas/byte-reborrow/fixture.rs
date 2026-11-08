pub fn replace_cell(cell: &mut u8, value: u8) -> u8 {
    let old = *cell;
    *cell = value;
    old
}

pub fn replace_at(bytes: &mut [u8], index: usize, value: u8) -> Option<u8> {
    if index < bytes.len() {
        let cell = &mut bytes[index];
        Some(replace_cell(cell, value))
    } else {
        None
    }
}
