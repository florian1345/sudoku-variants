use std::iter::Peekable;

use crate::util::USizeSet;

/// Recursively enters all options to build the required sum from the remaining
/// cells into `new_options`. Cells are required not to contain repeated
/// digits.
///
/// # Arguments
///
/// * `missing`: An iterator which yields one [USizeSet] for each missing cell
/// containing its options.
/// * `current_sum`: The sum accumulated so far from the previous cells, i.e.
/// all cells that were already filled and all that have been inserted.
/// * `required_sum`: The required sum for all cells.
/// * `new_options`: A vector which contains one [USizeSet] for each remaining
/// cell (same indices as `missing`). In this set all found options for that
/// specific cell should be entered.
/// * `numbers`: A [USizeSet] that contains all numbers that were already
/// inserted into previous cells in the cage. Filled cells are not considered
/// here, since those should not occur in the options in the first place.
/// * `index`: The index of the cell to process at this recursion depth.
fn find_options_unique_rec<'a, I>(mut missing: I, current_sum: usize,
    required_sum: usize, new_options: &mut [USizeSet],
    numbers: &mut USizeSet) -> bool
where
    I: ExactSizeIterator<Item = &'a USizeSet> + Clone
{
    let options = missing.next().unwrap();

    if missing.len() == 0 {
        let required = required_sum - current_sum;

        if options.contains(required) && !numbers.contains(required) {
            new_options[0].insert(required).unwrap();
            return true;
        }

        return false;
    }

    let mut result = false;

    for option in options.iter() {
        let next_sum = current_sum + option;

        if next_sum >= required_sum {
            // Options are in ascending order, so following options will only
            // be worse.
            break;
        }

        if numbers.contains(option) {
            continue;
        }

        numbers.insert(option).unwrap();

        if find_options_unique_rec(missing.clone(), next_sum, required_sum,
                &mut new_options[1..], numbers) {
            new_options[0].insert(option).unwrap();
            result = true;
        }

        numbers.remove(option).unwrap();
    }

    result
}

fn find_options<'a, I, F>(missing: I, current_sum: usize, required_sum: usize,
    rec_finder: F) -> Vec<USizeSet>
where
    I: ExactSizeIterator<Item = &'a USizeSet>,
    F: Fn(Peekable<I>, usize, usize, &mut [USizeSet]) -> bool
{
    let mut missing = missing.peekable();

    match missing.peek() {
        None => Vec::new(),
        Some(set) => {
            let lower = set.lower();
            let upper = set.upper();
            let mut new_options =
                vec![USizeSet::new(lower, upper).unwrap(); missing.len()];

            if current_sum < required_sum {
                rec_finder(missing, current_sum,
                    required_sum, &mut new_options);
            }
        
            new_options
        }
    }
}

/// Collects all possible options for a group of cells that must reach a given
/// sum, where a part of that sum may already have been made by other cells.
/// This method requires digits in the cells to be unique, i.e. no digit may
/// repeat in the `missing` cells.
///
/// # Arguments
///
/// * `missing`: The cell options of the cells participating in the sum, which
/// are missing from the current sum.
/// * `current_sum`: The sum already reached by known cells, which are not
/// given as input to this function.
/// * `required_sum`: The required sum for all cells - the missing ones and the
/// ones composing `current_sum`.
///
/// # Returns
///
/// A vector containing the options of the missing cells after considering the
/// sum constraint. The order is equal to the one in `missing`.
pub(crate) fn find_options_unique<'a, I>(missing: I, current_sum: usize,
    required_sum: usize) -> Vec<USizeSet>
where
    I: ExactSizeIterator<Item = &'a USizeSet> + Clone
{
    find_options(missing, current_sum, required_sum,
        |missing, current_sum, required_sum, new_options| {
            let lower = new_options[0].lower();
            let upper = new_options[0].upper();
            let mut numbers = USizeSet::new(lower, upper).unwrap();
            find_options_unique_rec(missing, current_sum, required_sum,
                new_options, &mut numbers)
        })
}

// TODO improve performance with short-circuiting

pub(crate) fn is_possible_unique<'a, I>(missing: I, current_sum: usize,
    required_sum: usize) -> bool
where
    I: ExactSizeIterator<Item = &'a USizeSet> + Clone
{
    if missing.len() == 0 {
        return current_sum == required_sum;
    }

    find_options_unique(missing, current_sum, required_sum).iter()
        .all(|s| !s.is_empty())
}

// TODO avoid code duplication with find_options_unique_rec

/// Recursively enters all options to build the required sum from the remaining
/// cells into `new_options`. Cells may contain repeated digits.
///
/// # Arguments
///
/// * `missing`: An iterator which yields one [USizeSet] for each missing cell
/// containing its options.
/// * `current_sum`: The sum accumulated so far from the previous cells, i.e.
/// all cells that were already filled and all that have been inserted.
/// * `required_sum`: The required sum for all cells.
/// * `new_options`: A vector which contains one [USizeSet] for each remaining
/// cell (same indices as `missing`). In this set all found options for that
/// specific cell should be entered.
/// * `index`: The index of the cell to process at this recursion depth.
fn find_options_repeat_rec<'a, I>(mut missing: I, current_sum: usize,
    required_sum: usize, new_options: &mut [USizeSet]) -> bool
where
    I: ExactSizeIterator<Item = &'a USizeSet> + Clone
{
    let options = missing.next().unwrap();

    if missing.len() == 0 {
        let required = required_sum - current_sum;

        if options.contains(required) {
            new_options[0].insert(required).unwrap();
            return true;
        }

        return false;
    }

    let mut result = false;

    for option in options.iter() {
        let next_sum = current_sum + option;

        if next_sum >= required_sum {
            // Options are in ascending order, so following options will only
            // be worse.
            break;
        }

        if find_options_repeat_rec(missing.clone(), next_sum, required_sum,
                &mut new_options[1..]) {
            new_options[0].insert(option).unwrap();
            result = true;
        }
    }

    result
}

/// Collects all possible options for a group of cells that must reach a given
/// sum, where a part of that sum may already have been made by other cells.
/// This method does not require digits in the cells to be unique, i.e. digits
/// may repeat in the `missing` cells.
///
/// # Arguments
///
/// * `missing`: The cell options of the cells participating in the sum, which
/// are missing from the current sum.
/// * `current_sum`: The sum already reached by known cells, which are not
/// given as input to this function.
/// * `required_sum`: The required sum for all cells - the missing ones and the
/// ones composing `current_sum`.
///
/// # Returns
///
/// A vector containing the options of the missing cells after considering the
/// sum constraint. The order is equal to the one in `missing`.
pub(crate) fn find_options_repeat<'a, I>(missing: I, current_sum: usize,
    required_sum: usize) -> Vec<USizeSet>
where
    I: ExactSizeIterator<Item = &'a USizeSet> + Clone
{
    find_options(missing, current_sum, required_sum, find_options_repeat_rec)
}

// TODO improve performance with short-circuiting

pub(crate) fn is_possible_repeat<'a, I>(missing: I, current_sum: usize,
    required_sum: usize) -> bool
where
    I: ExactSizeIterator<Item = &'a USizeSet> + Clone
{
    if missing.len() == 0 {
        return current_sum == required_sum;
    }

    find_options_repeat(missing, current_sum, required_sum).iter()
        .all(|s| !s.is_empty())
}

#[cfg(test)]
mod tests {

    use crate::set;

    use std::iter;

    use super::*;

    #[test]
    fn empty_input_unique() {
        assert_eq!(Vec::<USizeSet>::new(),
            find_options_unique(iter::empty(), 0, 0));
        assert_eq!(Vec::<USizeSet>::new(),
            find_options_unique(iter::empty(), 1, 5));
        assert!(is_possible_unique(iter::empty(), 0, 0));
        assert!(is_possible_unique(iter::empty(), 5, 5));
        assert!(!is_possible_unique(iter::empty(), 1, 5));
    }

    fn get_test_sets() -> Vec<USizeSet> {
        // Possible sums - (*) require repetition
        //  7 (*) - 2, 2, 3
        //  8 (*) - 2, 2, 4 - 3, 2, 3
        //  9     - 3, 2, 4
        // 12 (*) - 2, 2, 8
        // 13     - 2, 8, 3 - 3, 2, 8
        // 14     - 2, 8, 4 - 3, 8, 3
        // 15     - 3, 8, 4
        // 18 (*) - 2, 8, 8
        // 19 (*) - 3, 8, 8

        let mut sets = Vec::new();
        sets.push(set!(1, 9; 2, 3));
        sets.push(set!(1, 9; 2, 8));
        sets.push(set!(1, 9; 3, 4, 8));
        sets
    }

    #[test]
    fn impossible_unique() {
        assert_eq!(vec![USizeSet::new(1, 9).unwrap(); 3],
            find_options_unique(get_test_sets().iter(), 0, 6));
        assert_eq!(vec![USizeSet::new(1, 9).unwrap(); 3],
            find_options_unique(get_test_sets().iter(), 5, 17));
        assert!(!is_possible_unique(get_test_sets().iter(), 0, 0));
        assert!(!is_possible_unique(get_test_sets().iter(), 2, 20));
    }

    #[test]
    fn possible_unique() {
        let mut sets_9 = Vec::new();
        sets_9.push(set!(1, 9; 3));
        sets_9.push(set!(1, 9; 2));
        sets_9.push(set!(1, 9; 4));

        let mut sets_13 = Vec::new();
        sets_13.push(set!(1, 9; 2, 3));
        sets_13.push(set!(1, 9; 2, 8));
        sets_13.push(set!(1, 9; 3, 8));

        assert_eq!(&sets_9,
            &find_options_unique(get_test_sets().iter(), 0, 9));
        assert_eq!(&sets_13,
            &find_options_unique(get_test_sets().iter(), 7, 20));
        assert!(is_possible_unique(get_test_sets().iter(), 0, 14));
        assert!(is_possible_unique(get_test_sets().iter(), 5, 20));
    }

    #[test]
    fn empty_input_repeat() {
        assert_eq!(Vec::<USizeSet>::new(),
            find_options_repeat(iter::empty(), 0, 0));
        assert_eq!(Vec::<USizeSet>::new(),
            find_options_repeat(iter::empty(), 2, 3));
        assert!(is_possible_repeat(iter::empty(), 0, 0));
        assert!(is_possible_repeat(iter::empty(), 6, 6));
        assert!(!is_possible_repeat(iter::empty(), 2, 3));
    }

    #[test]
    fn impossible_repeat() {
        assert_eq!(vec![USizeSet::new(1, 9).unwrap(); 3],
            find_options_repeat(get_test_sets().iter(), 0, 6));
        assert_eq!(vec![USizeSet::new(1, 9).unwrap(); 3],
            find_options_repeat(get_test_sets().iter(), 5, 16));
        assert!(!is_possible_repeat(get_test_sets().iter(), 0, 0));
        assert!(!is_possible_repeat(get_test_sets().iter(), 2, 18));
    }

    #[test]
    fn possible_repeat() {
        let mut sets_8 = Vec::new();
        sets_8.push(set!(1, 9; 2, 3));
        sets_8.push(set!(1, 9; 2));
        sets_8.push(set!(1, 9; 3, 4));

        let mut sets_14 = Vec::new();
        sets_14.push(set!(1, 9; 2, 3));
        sets_14.push(set!(1, 9; 8));
        sets_14.push(set!(1, 9; 3, 4));

        assert_eq!(&sets_8,
            &find_options_repeat(get_test_sets().iter(), 0, 8));
        assert_eq!(&sets_14,
            &find_options_repeat(get_test_sets().iter(), 7, 21));
        assert!(is_possible_repeat(get_test_sets().iter(), 0, 9));
        assert!(is_possible_repeat(get_test_sets().iter(), 2, 20));
    }
}
