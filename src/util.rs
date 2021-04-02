//! This module contains utility functionality needed for this crate. Most
//! prominently, it contains the definition of the [USizeSet] used for storing
//! cell options for strategies.

use std::collections::HashSet;
use std::hash::Hash;
use std::mem;
use std::ops::{
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
    Sub,
    SubAssign
};
use std::slice::Iter;

/// A set of `usize` that is implemented as a bit vector. Each `usize` that is
/// in the range of possible elements is represented by one bit in a vector of
/// numbers. This generally has better performance than a `HashSet`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct USizeSet {
    min: usize,
    max: usize,
    len: usize,
    content: Vec<u64>
}

/// An enumeration of the errors that can happen when using a [USizeSet].
#[derive(Debug, Eq, PartialEq)]
pub enum USizeSetError {

    /// Indicates that the bounds provided in the constructor are invalid, that
    /// is, the minimum is greater than the maximum.
    InvalidBounds,

    /// Indicates that an operation was performed on two or more `USizeSet`s
    /// with different bounds.
    DifferentBounds,

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

/// An iterator over the content of a [USizeSet].
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

    /// Inserts the given number into this set, such that [USizeSet::contains]
    /// returns `true` for this number afterwards. Note that it must be within
    /// the bounds provided at construction time.
    ///
    /// This method returns `true` if the set has changed (i.e. the number was
    /// not present before) and `false` otherwise.
    ///
    /// # Errors
    ///
    /// If `number` is less than [USizeSet::min] or greater than
    /// [USizeSet::max]. In that case, `USizeSetError::OutOfBounds` is
    /// returned.
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

    /// Removes the given number from this set, such that [USizeSet::contains]
    /// returns `false` for this number afterwards. Note that it must be within
    /// the bounds provided at construction time.
    ///
    /// This method returns `true` if the set has changed (i.e. the number was
    /// present before) and `false` otherwise.
    ///
    /// # Errors
    ///
    /// If `number` is less than [USizeSet::min] or greater than
    /// [USizeSet::max]. In that case, `USizeSetError::OutOfBounds` is
    /// returned.
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

    /// Removes all numbers from this set, such that [USizeSet::contains] will
    /// return `false` for all inputs and [USizeSet::is_empty] will return
    /// `true`.
    pub fn clear(&mut self) {
        for i in 0..self.content.len() {
            self.content[i] = 0;
        }

        self.len = 0;
    }

    /// Returns an iterator over the numbers contained in this set in ascending
    /// order.
    pub fn iter(&self) -> USizeSetIter<'_> {
        USizeSetIter::new(self)
    }

    /// Indicates whether this set is empty, i.e. contains no numbers. If this
    /// method returns `true`, [USizeSet::contains] will return `false` for all
    /// inputs.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the number of elements contained in this set.
    pub fn len(&self) -> usize {
        self.len
    }

    fn count(&self) -> usize {
        self.content.iter()
            .map(|c| c.count_ones() as usize)
            .sum()
    }

    fn op_assign(&mut self, other: &USizeSet, op: impl Fn(u64, u64) -> u64)
            -> USizeSetResult<bool> {
        if self.min() != other.min() || self.max() != other.max() {
            Err(USizeSetError::DifferentBounds)
        }
        else {
            let contents = self.content.iter_mut().zip(other.content.iter());
            let mut changed = false;

            for (self_u64, &other_u64) in contents {
                let self_before = *self_u64;
                *self_u64 = op(self_before, other_u64);
                changed |= self_before != *self_u64;
            }

            self.len = self.count();
            Ok(changed)
        }
    }

    fn op(&self, other: &USizeSet,
            op_assign: impl Fn(&mut USizeSet, &USizeSet) -> USizeSetResult<bool>)
            -> USizeSetResult<USizeSet> {
        let mut clone = self.clone();
        op_assign(&mut clone, other)?;
        Ok(clone)
    }

    /// Computes the set union between this and the given set and stores the
    /// result in this set. The bounds of this set and `other` must be equal.
    ///
    /// `USizeSet` implements [BitOrAssign] as syntactic sugar for this
    /// operation. Note that that implementation panics instead of returning
    /// potential errors.
    ///
    /// # Returns
    ///
    /// True, if and only if this set changed as a result of the operation.
    ///
    /// # Errors
    ///
    /// If either the minimum or maximum of this set and `other` are different.
    /// In that case, `USizeError::DifferentBounds` is returned.
    pub fn union_assign(&mut self, other: &USizeSet) -> USizeSetResult<bool> {
        self.op_assign(other, u64::bitor)
    }

    /// Computes the set union between this and the given set and stores the
    /// result in a new set which is returned. The bounds of this set and
    /// `other` must be equal.
    ///
    /// `USizeSet` implements [BitOr] as syntactic sugar for this operation.
    /// Note that that implementation  panics instead of returning potential
    /// errors.
    ///
    /// # Errors
    ///
    /// If the minimum or maximum of this set and `other` are different. In
    /// that case, `USizeError::DifferentBounds` is returned.
    pub fn union(&self, other: &USizeSet) -> USizeSetResult<USizeSet> {
        self.op(other, USizeSet::union_assign)
    }

    /// Computes the set intersection between this and the given set and stores
    /// the result in this set. The bounds of this set and `other` must be
    /// equal.
    ///
    /// `USizeSet` implements [BitAndAssign] as syntactic sugar for this
    /// operation. Note that that implementation panics instead of returning
    /// potential errors.
    ///
    /// # Returns
    ///
    /// True, if and only if this set changed as a result of the operation.
    ///
    /// # Errors
    ///
    /// If the minimum or maximum of this set and `other` are different. In
    /// that case, `USizeError::DifferentBounds` is returned.
    pub fn intersect_assign(&mut self, other: &USizeSet)
            -> USizeSetResult<bool> {
        self.op_assign(other, u64::bitand)
    }

    /// Computes the set intersection between this and the given set and stores
    /// the result in a new set which is returned. The bounds of this set and
    /// `other` must be equal.
    ///
    /// `USizeSet` implements [BitAnd] as syntactic sugar for this operation.
    /// Note that that implementation panics instead of returning potential
    /// errors.
    ///
    /// # Errors
    ///
    /// If the minimum or maximum of this set and `other` are different. In
    /// that case, `USizeError::DifferentBounds` is returned.
    pub fn intersect(&self, other: &USizeSet) -> USizeSetResult<USizeSet> {
        self.op(other, USizeSet::intersect_assign)
    }

    /// Computes the set difference between this and the given set and stores
    /// the result in this set. The bounds of this set and `other` must be
    /// equal. `other` acts as the right-hand-side, meaning its elements are
    /// removed from the result.
    ///
    /// `USizeSet` implements [SubAssign] as syntactic sugar for this
    /// operation. Note that that implementation panics instead of returning
    /// potential errors.
    ///
    /// # Returns
    ///
    /// True, if and only if this set changed as a result of the operation.
    ///
    /// # Errors
    ///
    /// If the minimum or maximum of this set and `other` are different. In
    /// that case, `USizeError::DifferentBounds` is returned.
    pub fn difference_assign(&mut self, other: &USizeSet)
            -> USizeSetResult<bool> {
        self.op_assign(other, |a, b| a & !b)
    }

    /// Computes the set difference between this and the given set and stores
    /// the result in a new set which is returned. The bounds of this set and
    /// `other` must be equal.
    ///
    /// `USizeSet` implements [Sub] as syntactic sugar for this operation. Note
    /// that that implementation panics instead of returning potential errors.
    ///
    /// # Errors
    ///
    /// If the minimum or maximum of this set and `other` are different. In
    /// that case, `USizeError::DifferentBounds` is returned.
    pub fn difference(&self, other: &USizeSet) -> USizeSetResult<USizeSet> {
        self.op(other, USizeSet::difference_assign)
    }

    /// Computes the symmetric set difference between this and the given set
    /// and stores the result in this set. The bounds of this set and `other`
    /// must be equal.
    ///
    /// `USizeSet` implements [BitXorAssign] as syntactic sugar for this
    /// operation. Note that that implementation panics instead of returning
    /// potential errors.
    ///
    /// # Returns
    ///
    /// True, if and only if this set changed as a result of the operation.
    ///
    /// # Errors
    ///
    /// If the minimum or maximum of this set and `other` are different. In
    /// that case, `USizeError::DifferentBounds` is returned.
    pub fn symmetric_difference_assign(&mut self, other: &USizeSet)
            -> USizeSetResult<bool> {
        self.op_assign(other, u64::bitxor)
    }

    /// Computes the symmetric set difference between this and the given set
    /// and stores the result in a new set which is returned. The bounds of
    /// this set and `other` must be equal.
    ///
    /// `USizeSet` implements [BitXor] as syntactic sugar for this operation.
    /// Note that that implementation panics instead of returning potential
    /// errors.
    ///
    /// # Errors
    ///
    /// If the minimum or maximum of this set and `other` are different. In
    /// that case, `USizeError::DifferentBounds` is returned.
    pub fn symmetric_difference(&self, other: &USizeSet)
            -> USizeSetResult<USizeSet> {
        self.op(other, USizeSet::symmetric_difference_assign)
    }
}

/// Creates a new [USizeSet] that contains the specified elements. First, the
/// minimum and maximum values must be specified. Then, after a semicolon, a
/// comma-separated list of the contained values must be provided. For empty
/// sets, [USizeSet.new()] can be used.
///
/// An example usage of this macro looks as follows:
///
/// ```
/// use sudoku_variants::set;
/// use sudoku_variants::util::USizeSet;
///
/// let set = set!(1, 5; 2, 4);
/// assert_eq!(1, set.min());
/// assert_eq!(5, set.max());
/// assert!(set.contains(2));
/// assert!(!set.contains(3));
/// ```
#[macro_export]
macro_rules! set {
    ($set:expr; $e:expr) => {
        ($set).insert($e).unwrap()
    };

    ($set:expr; $e:expr, $($es:expr),+) => {
        set!($set; $e);
        set!($set; $($es),+)
    };

    ($min:expr, $max:expr; $($es:expr),+) => {
        {
            let mut set = USizeSet::new($min, $max).unwrap();
            set!(set; $($es),+);
            set
        }
    };
}

impl BitAnd<&USizeSet> for USizeSet {
    type Output = USizeSet;

    fn bitand(mut self, rhs: &USizeSet) -> USizeSet {
        self.intersect_assign(rhs).unwrap();
        self
    }
}

impl BitOr<&USizeSet> for USizeSet {
    type Output = USizeSet;

    fn bitor(mut self, rhs: &USizeSet) -> USizeSet {
        self.union_assign(rhs).unwrap();
        self
    }
}

impl Sub<&USizeSet> for USizeSet {
    type Output = USizeSet;

    fn sub(mut self, rhs: &USizeSet) -> USizeSet {
        self.difference_assign(rhs).unwrap();
        self
    }
}

impl BitXor<&USizeSet> for USizeSet {
    type Output = USizeSet;

    fn bitxor(mut self, rhs: &USizeSet) -> USizeSet {
        self.symmetric_difference_assign(rhs).unwrap();
        self
    }
}

impl BitAnd for &USizeSet {
    type Output = USizeSet;

    fn bitand(self, rhs: &USizeSet) -> USizeSet {
        self.intersect(rhs).unwrap()
    }
}

impl BitOr for &USizeSet {
    type Output = USizeSet;

    fn bitor(self, rhs: &USizeSet) -> USizeSet {
        self.union(rhs).unwrap()
    }
}

impl Sub for &USizeSet {
    type Output = USizeSet;

    fn sub(self, rhs: &USizeSet) -> USizeSet {
        self.difference(rhs).unwrap()
    }
}

impl BitXor for &USizeSet {
    type Output = USizeSet;

    fn bitxor(self, rhs: &USizeSet) -> USizeSet {
        self.symmetric_difference(rhs).unwrap()
    }
}

impl BitAndAssign<&USizeSet> for USizeSet {
    fn bitand_assign(&mut self, rhs: &USizeSet) {
        self.intersect_assign(rhs).unwrap();
    }
}

impl BitOrAssign<&USizeSet> for USizeSet {
    fn bitor_assign(&mut self, rhs: &USizeSet) {
        self.union_assign(rhs).unwrap();
    }
}

impl SubAssign<&USizeSet> for USizeSet {
    fn sub_assign(&mut self, rhs: &USizeSet) {
        self.difference_assign(rhs).unwrap();
    }
}

impl BitXorAssign<&USizeSet> for USizeSet {
    fn bitxor_assign(&mut self, rhs: &USizeSet) {
        self.symmetric_difference_assign(rhs).unwrap();
    }
}

impl BitAndAssign<&USizeSet> for &mut USizeSet {
    fn bitand_assign(&mut self, rhs: &USizeSet) {
        self.intersect_assign(rhs).unwrap();
    }
}

impl BitOrAssign<&USizeSet> for &mut USizeSet {
    fn bitor_assign(&mut self, rhs: &USizeSet) {
        self.union_assign(rhs).unwrap();
    }
}

impl SubAssign<&USizeSet> for &mut USizeSet {
    fn sub_assign(&mut self, rhs: &USizeSet) {
        self.difference_assign(rhs).unwrap();
    }
}

impl BitXorAssign<&USizeSet> for &mut USizeSet {
    fn bitxor_assign(&mut self, rhs: &USizeSet) {
        self.symmetric_difference_assign(rhs).unwrap();
    }
}

/// Determines whether the given iterator contains at least two equal elements
/// as defined by the [Eq](std::cmp::Eq) trait. The duplication detection is
/// implemented with a [HashSet](std::collections::HashSet), so it is required
/// that the item type implements the [Hash](std::hash::Hash) trait in a
/// consistent way.
pub(crate) fn contains_duplicate<I>(mut iter: I) -> bool
where
    I: Iterator,
    I::Item: Hash + Eq
{
    let mut set = HashSet::new();
    iter.any(|e| !set.insert(e))
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
    fn set_macro_has_specified_range() {
        let set = set!(2, 5; 3);
        assert_eq!(2, set.min());
        assert_eq!(5, set.max());
    }

    #[test]
    fn set_macro_contains_specified_elements() {
        let set = set!(2, 8; 3, 7, 8);
        assert_eq!(3, set.len());
        assert!(set.contains(3));
        assert!(set.contains(7));
        assert!(set.contains(8));
        assert!(!set.contains(5));
    }

    #[test]
    fn set_creation_error() {
        assert_eq!(Err(USizeSetError::InvalidBounds), USizeSet::new(1, 0));
        assert_eq!(Err(USizeSetError::InvalidBounds), USizeSet::new(5, 3));
    }

    #[test]
    fn set_insertion_error() {
        let mut set = USizeSet::new(1, 5).unwrap();
        assert_eq!(Err(USizeSetError::OutOfBounds), set.insert(0));
        assert_eq!(Err(USizeSetError::OutOfBounds), set.insert(6));
    }

    #[test]
    fn set_operation_error() {
        let set_1 = USizeSet::new(1, 9).unwrap();
        let set_2 = USizeSet::new(1, 6).unwrap();
        assert_eq!(Err(USizeSetError::DifferentBounds), set_1.union(&set_2));
        assert_eq!(Err(USizeSetError::DifferentBounds),
            set_2.intersect(&set_1));
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

    fn op_test_lhs() -> USizeSet {
        set!(1, 4; 2, 4)
    }

    fn op_test_rhs() -> USizeSet {
        set!(1, 4; 3, 4)
    }

    #[test]
    fn union() {
        let result = op_test_lhs() | &op_test_rhs();
        let expected = set!(1, 4; 2, 3, 4);
        assert_eq!(expected, result);
    }

    #[test]
    fn intersection() {
        let result = op_test_lhs() & &op_test_rhs();
        let expected = set!(1, 4; 4);
        assert_eq!(expected, result);
    }

    #[test]
    fn difference() {
        let result = op_test_lhs() - &op_test_rhs();
        let expected = set!(1, 4; 2);
        assert_eq!(expected, result);
    }

    #[test]
    fn symmetric_difference() {
        let result = op_test_lhs() ^ &op_test_rhs();
        let expected = set!(1, 4; 2, 3);
        assert_eq!(expected, result);
    }

    #[test]
    fn contains_duplicate_false() {
        let vec = vec![1, 5, 2, 4, 3];
        assert!(!contains_duplicate(vec.iter()));
        assert!(!contains_duplicate(vec.iter().map(|i| i.to_string())));
    }

    #[test]
    fn contains_duplicate_true() {
        let vec = vec![1, 5, 2, 4, 5];
        assert!(contains_duplicate(vec.iter()));
        assert!(contains_duplicate(vec.iter().map(|i| i.to_string())));
    }
}
