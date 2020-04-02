use std::collections::BTreeMap;

pub fn group_by<'a, K, V>(
    iter: impl IntoIterator<Item = &'a V>,
    mut get_key: impl FnMut(&V) -> K,
) -> BTreeMap<K, Vec<&'a V>>
where
    K: Ord,
{
    let mut groups: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for item in iter {
        groups.entry(get_key(item)).or_default().push(item);
    }
    groups
}

/// Converts a bit vector (encoded as an array of bools) to a string of '0's and '1's
pub fn bool_to_char(value: bool) -> char {
    match value {
        true => '1',
        false => '0',
    }
}

/// Converts a bit vector (encoded as an array of bools) to a string of '0's and '1's
pub fn bits_to_string(bits: &[bool]) -> String {
    bits.iter().map(|&x| bool_to_char(x)).collect()
}

/// Finds the offset of the first true bit
pub fn first_bit(bits: &[bool]) -> usize {
    bits.iter().position(|&p| p).expect("Expected at least one true bit")
}

/// Generates a bit mask for a given offset and length
pub fn get_mask(offset: usize, len: usize) -> Vec<bool> {
    std::iter::repeat(false).take(offset).chain(std::iter::repeat(true).take(len)).collect()
}

#[allow(dead_code)]
pub fn debug_key(key: &[bool], used: &[bool]) -> String {
    let len = used.len().max(key.len());
    let mut output = String::with_capacity(len);

    for i in 0..len {
        let used_bit = *used.get(i).unwrap_or(&false);
        let value = *key.get(i).unwrap_or(&false);

        if used_bit {
            output.push(if value { '1' } else { '0' });
        }
        else {
            output.push('_');
        }
    }

    output
}
