use std::mem;
use std::slice::Iter;

/// A set of `usize` that is implemented as a bit vector. Each `usize` that is
/// in the range of possible elements is represented by one bit in a vector of
/// numbers. This generally has better performance than a `HashSet`.
#[derive(Clone, Eq, PartialEq)]
pub struct USizeSet {
    min: usize,
    max: usize,
    len: usize,
    content: Vec<u64>
}

/// An enumeration of the errors that can happen when using a
/// [USizeSet](struct.USizeSet.html).
#[derive(Debug)]
pub enum USizeSetError {

    /// Indicates that the bounds provided in the constructor are invalid, that
    /// is, the minimum is greater than the maximum.
    InvalidBounds,

    /// Indicates that a number that was queried to be inserted or removed is
    /// out of the bounds of the `USizeSet` in question.
    OutOfBounds
}

/// Syntactic sugar for `Result<V, USizeSetError>`.
pub type USizeSetResult<V> = Result<V, USizeSetError>;

struct BitIterator {
    bit_index: usize,
    value: u64
}

impl BitIterator {
    fn new(value: u64) -> BitIterator {
        BitIterator {
            bit_index: 0,
            value
        }
    }

    fn progress(&mut self) {
        let diff = self.value.trailing_zeros() as usize;
        self.value >>= diff;
        self.bit_index += diff;
    }
}

impl Iterator for BitIterator {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.value != 0 && (self.value & 1) == 0 {
            self.progress();
        }

        let result = if self.value == 0 { None } else { Some(self.bit_index) };
        self.value &= 0xfffffffffffffffe;
        result
    }
}

/// An iterator over the content of a [USizeSet](struct.USizeSet.html).
pub struct USizeSetIter<'a> {
    offset: usize,
    current: BitIterator,
    content: Iter<'a, u64>
}

impl<'a> USizeSetIter<'a> {
    fn new(set: &'a USizeSet) -> USizeSetIter<'a> {
        let mut iter = set.content.iter();
        let first_bit_iterator = if let Some(&first) = iter.next() {
            BitIterator::new(first)
        }
        else {
            BitIterator::new(0)
        };

        USizeSetIter {
            offset: set.min,
            current: first_bit_iterator,
            content: iter
        }
    }
}

const USIZE_BIT_SIZE: usize = mem::size_of::<usize>() * 8;

impl<'a> Iterator for USizeSetIter<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        loop {
            if let Some(bit_index) = self.current.next() {
                return Some(self.offset + bit_index);
            }

            if let Some(&next_content) = self.content.next() {
                self.current = BitIterator::new(next_content);
                self.offset += USIZE_BIT_SIZE;
            }
            else {
                return None;
            }
        }
    }
}

impl USizeSet {

    /// Creates a new, empty `USizeSet` with the given (inclusive) bounds.
    ///
    /// # Arguments
    ///
    /// * `min`: The minimum value that can be contained in the created set.
    /// Any values lower than that will yield a `USizeSetError::OutOfBounds` if
    /// inserted or removed. Must be less than or equal to `max`.
    /// * `max`: The maximum value that can be contained in the created set.
    /// Any values higher than that will yield a `USizeSetError::OutOfBounds`
    /// if inserted or removed. Must be greater than or equal to `min`.
    ///
    /// # Errors
    ///
    /// If `min > max`. In that case, a `USizeSetError::InvalidBounds` is
    /// returned.
    pub fn new(min: usize, max: usize) -> USizeSetResult<USizeSet> {
        if min > max {
            Err(USizeSetError::InvalidBounds)
        }
        else {
            let required_words = (max - min + 64) >> 6;

            Ok(USizeSet {
                min,
                max,
                len: 0,
                content: vec![0u64; required_words]
            })
        }
    }

    /// Creates a new singleton `USizeSet` with the given (inclusive) bounds.
    /// The set contains one element, which is specified by `content`.
    ///
    /// # Arguments
    ///
    /// * `min`: The minimum value that can be contained in the created set.
    /// Any values lower than that will yield a `USizeSetError::OutOfBounds` if
    /// inserted or removed. Must be less than or equal to `max`.
    /// * `max`: The maximum value that can be contained in the created set.
    /// Any values higher than that will yield a `USizeSetError::OutOfBounds`
    /// if inserted or removed. Must be greater than or equal to `min`.
    /// * `content`: The only element contained by the created set. Must be
    /// within the bounds.
    ///
    /// # Errors
    ///
    /// * `USizeSetError::InvalidBounds`: If `min > max`.
    /// * `USizeSetError::OutOfBounds`: If `content < min` or `content > max`.
    pub fn singleton(min: usize, max: usize, content: usize)
            -> USizeSetResult<USizeSet> {
        let mut result = USizeSet::new(min, max)?;
        result.insert(content)?;
        Ok(result)
    }

    /// Creates a new `USizeSet` that includes all numbers in the given
    /// (inclusive) bounds. Note that these bounds also apply later.
    ///
    /// # Arguments
    ///
    /// * `min`: The minimum value contained in the created set, which is also
    /// the minimum that can be contained. Any values lower than this will
    /// yield a `USizeSetError::OutOfBounds` if inserted or removed. Must be
    /// less than or equal to `max`.
    /// * `max`: The maximum value contained in the created set, which is also
    /// the maximum value that can be contained. Any values higher than this
    /// will yield a `USizeSetError::OutOfBounds` if inserted or removed. Must
    /// be greater than or equal to `min`.
    ///
    /// # Errors
    ///
    /// If `min > max`. In that case, a `USizeSetError::InvalidBounds` is
    /// returned.
    pub fn range(min: usize, max: usize) -> USizeSetResult<USizeSet> {
        if min > max {
            Err(USizeSetError::InvalidBounds)
        }
        else {
            let mut content = Vec::new();
            let ones = max - min + 1;
            let ones_words = ones >> 6;

            for _ in 1..ones_words {
                content.push(!0);
            }

            let remaining_ones = ones - (ones_words << 6);

            if remaining_ones > 0 {
                content.push((1 << remaining_ones) - 1);
            }

            Ok(USizeSet {
                min,
                max,
                len: ones,
                content
            })
        }
    }

    fn compute_index(&self, number: usize) -> USizeSetResult<(usize, u64)> {
        if number < self.min || number > self.max {
            Err(USizeSetError::OutOfBounds)
        }
        else {
            let index = number - self.min;
            let word_index = index >> 6;
            let sub_word_index = index & 63;
            let mask = 1u64 << sub_word_index;
            Ok((word_index, mask))
        }
    }

    /// Returns the minimum value that this set can contain (inclusive).
    pub fn min(&self) -> usize {
        self.min
    }

    /// Returns the maximum value that this set can contain (inclusive).
    pub fn max(&self) -> usize {
        self.max
    }

    /// Indicates whether this set contains the given number, in which case
    /// this method returns `true`. If it is not contained or outside the
    /// bounds, `false` will be returned.
    pub fn contains(&self, number: usize) -> bool {
        if let Ok((word_index, mask)) = self.compute_index(number) {
            (self.content[word_index] & mask) > 0
        }
        else {
            false
        }
    }

    /// Inserts the given number into this set, such that
    /// [USizeSet.contains](#method.contains) returns `true` for this number
    /// afterwards. Note that it must be within the bounds provided at
    /// construction time.
    ///
    /// This method returns `true` if the set has changed (i.e. the number was
    /// not present before) and `false` otherwise.
    ///
    /// # Errors
    ///
    /// If `number` is less than [USizeSet.min](#method.min) or greater than
    /// [USizeSet.max](#method.max). In that case, `USizeSetError::OutOfBounds`
    /// is returned.
    pub fn insert(&mut self, number: usize) -> USizeSetResult<bool> {
        let (word_index, mask) = self.compute_index(number)?;
        let word = &mut self.content[word_index];

        if *word & mask == 0 {
            self.len += 1;
            *word |= mask;
            Ok(true)
        }
        else {
            Ok(false)
        }
    }

    /// Removes the given number from this set, such that
    /// [USizeSet.contains](#method.contains) returns `false` for this number
    /// afterwards. Note that it must be within the bounds provided at
    /// construction time.
    ///
    /// This method returns `true` if the set has changed (i.e. the number was
    /// present before) and `false` otherwise.
    ///
    /// # Errors
    ///
    /// If `number` is less than [USizeSet.min](#method.min) or greater than
    /// [USizeSet.max](#method.max). In that case, `USizeSetError::OutOfBounds`
    /// is returned.
    pub fn remove(&mut self, number: usize) -> USizeSetResult<bool> {
        let (word_index, mask) = self.compute_index(number)?;
        let word = &mut self.content[word_index];

        if *word & mask > 0 {
            *word &= !mask;
            self.len -= 1;
            Ok(true)
        }
        else {
            Ok(false)
        }
    }

    /// Removes all numbers from this set, such that
    /// [USizeSet.contains](#method.contains) will return `false` for all
    /// inputs and [USizeSet.is_empty](#method.is_empty) will return `true`.
    pub fn clear(&mut self) {
        for i in 0..self.content.len() {
            self.content[i] = 0;
        }

        self.len = 0;
    }

    /// Returns an iterator over the numbers contained in this set in ascending
    /// order.
    pub fn iter<'a>(&'a self) -> USizeSetIter<'a> {
        USizeSetIter::new(self)
    }

    /// Indicates whether this set is empty, i.e. contains no numbers. If this
    /// method returns `true`, [USizeSet.contains](#method.contains) will
    /// return `false` for all inputs.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the number of elements contained in this set.
    pub fn len(&self) -> usize {
        self.len
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn new_set_is_empty() {
        let set = USizeSet::new(1, 9).unwrap();
        assert!(set.is_empty());
        assert!(!set.contains(1));
        assert!(!set.contains(3));
        assert!(!set.contains(9));
        assert_eq!(0, set.len());
    }

    #[test]
    fn range_set_is_full() {
        let set = USizeSet::range(1, 9).unwrap();
        assert!(!set.is_empty());
        assert!(set.contains(1));
        assert!(set.contains(3));
        assert!(set.contains(9));
        assert_eq!(9, set.len());
    }

    #[test]
    fn singleton_set_contains_only_given_element() {
        let set = USizeSet::singleton(1, 9, 3).unwrap();
        assert!(!set.is_empty());
        assert!(!set.contains(1));
        assert!(set.contains(3));
        assert!(!set.contains(9));
        assert_eq!(1, set.len());
    }

    #[test]
    fn manipulation() {
        let mut set = USizeSet::new(1, 9).unwrap();
        set.insert(2).unwrap();
        set.insert(4).unwrap();
        set.insert(6).unwrap();

        assert!(!set.is_empty());
        assert!(set.contains(2));
        assert!(set.contains(4));
        assert!(set.contains(6));
        assert_eq!(3, set.len());

        set.remove(4).unwrap();

        assert!(!set.is_empty());
        assert!(set.contains(2));
        assert!(!set.contains(4));
        assert!(set.contains(6));
        assert_eq!(2, set.len());

        set.clear();

        assert!(set.is_empty());
        assert!(!set.contains(2));
        assert!(!set.contains(4));
        assert!(!set.contains(6));
        assert_eq!(0, set.len());
    }

    #[test]
    fn iteration() {
        let mut set = USizeSet::new(1, 100).unwrap();
        set.insert(1).unwrap();
        set.insert(12).unwrap();
        set.insert(23).unwrap();
        set.insert(36).unwrap();
        set.insert(42).unwrap();
        set.insert(64).unwrap();
        set.insert(65).unwrap();
        set.insert(97).unwrap();
        set.insert(100).unwrap();

        let mut iter = set.iter();

        assert_eq!(Some(1), iter.next());
        assert_eq!(Some(12), iter.next());
        assert_eq!(Some(23), iter.next());
        assert_eq!(Some(36), iter.next());
        assert_eq!(Some(42), iter.next());
        assert_eq!(Some(64), iter.next());
        assert_eq!(Some(65), iter.next());
        assert_eq!(Some(97), iter.next());
        assert_eq!(Some(100), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn double_insert() {
        let mut set = USizeSet::new(1, 9).unwrap();
        assert!(set.insert(3).unwrap());
        assert!(set.insert(4).unwrap());
        assert!(!set.insert(3).unwrap());

        assert!(set.contains(3));
        assert_eq!(2, set.len());
    }

    #[test]
    fn double_remove() {
        let mut set = USizeSet::range(1, 9).unwrap();
        assert!(set.remove(3).unwrap());
        assert!(set.remove(5).unwrap());
        assert!(!set.remove(3).unwrap());

        assert!(!set.contains(3));
        assert_eq!(7, set.len());
    }
}
