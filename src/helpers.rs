use std::collections::BTreeMap;

pub fn group_by<K, V>(
    iter: impl IntoIterator<Item = V>,
    mut get_key: impl FnMut(&V) -> K,
) -> BTreeMap<K, Vec<V>>
where
    K: Ord,
{
    let mut groups: BTreeMap<_, Vec<_>> = BTreeMap::new();
    for item in iter {
        groups.entry(get_key(&item)).or_default().push(item);
    }
    groups
}

/// Converts a bit vector (encoded as an array of bools) to a string of '0's and '1's
pub fn bits_to_string(bits: &[bool]) -> String {
    let cond = |&x| if x { '1' } else { '0' };
    bits.iter().map(cond).collect()
}

/// Finds the offset of the first true bit
pub fn first_bit(bits: &[bool]) -> usize {
    bits.iter().position(|&p| p).expect("Expected at least one true bit")
}

/// Generates a bit mask for a given offset and length
pub fn get_mask(offset: usize, len: usize) -> Vec<bool> {
    std::iter::repeat(false).take(offset).chain(std::iter::repeat(true).take(len)).collect()
}
