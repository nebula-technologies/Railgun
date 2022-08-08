use std::iter::FusedIterator;
use std::mem;

pub trait OptionsExtended<T> {
    /// Returns `true` if the option is a [`Some`] wrapping a value matching the predicate.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let x: Option<u32> = Some(2);
    /// assert_eq!(x.is_some_with(|&x| x > 1), true);
    ///
    /// let x: Option<u32> = Some(0);
    /// assert_eq!(x.is_some_with(|&x| x > 1), false);
    ///
    /// let x: Option<u32> = None;
    /// assert_eq!(x.is_some_with(|&x| x > 1), false);
    /// ```
    #[must_use]
    fn is_some_with(&self, f: impl FnOnce(&T) -> bool) -> bool;

    /// Calls the provided closure with a reference to the contained value (if [`Some`]).
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let v = vec![1, 2, 3, 4, 5];
    ///
    /// // prints "got: 4"
    /// let x: Option<&usize> = v.get(3).inspect(|x| println!("got: {}", x));
    ///
    /// // prints nothing
    /// let x: Option<&usize> = v.get(5).inspect(|x| println!("got: {}", x));
    /// ```
    fn inspect<F>(self, f: F) -> Self
        where
            F: FnOnce(&T);

    /////////////////////////////////////////////////////////////////////////
    // Iterator constructors
    /////////////////////////////////////////////////////////////////////////

    /// Returns an iterator over the possibly contained value.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    /// let x = Some(4);
    /// assert_eq!(x.iter().next(), Some(&4));
    ///
    /// let x: Option<u32> = None;
    /// assert_eq!(x.iter().next(), None);
    /// ```
    fn iter(&self) -> Iter<'_, T>;

    /////////////////////////////////////////////////////////////////////////
    // Entry-like operations to insert a value and return a reference
    /////////////////////////////////////////////////////////////////////////

    /// Inserts `value` into the option, then returns a mutable reference to it.
    ///
    /// If the option already contains a value, the old value is dropped.
    ///
    /// See also [`Option::get_or_insert`], which doesn't update the value if
    /// the option already contains [`Some`].
    ///
    /// # Example
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    /// let mut opt = None;
    /// let val = opt.insert(1);
    /// assert_eq!(*val, 1);
    /// assert_eq!(opt.unwrap(), 1);
    /// let val = opt.insert(2);
    /// assert_eq!(*val, 2);
    /// *val = 3;
    /// assert_eq!(opt.unwrap(), 3);
    /// ```
    #[must_use = "if you intended to set a value, consider assignment instead"]
    fn insert(&mut self, value: T) -> &mut T
        where
            T: Drop;

    /// Inserts `value` into the option if it is [`None`], then
    /// returns a mutable reference to the contained value.
    ///
    /// See also [`Option::insert`], which updates the value even if
    /// the option already contains [`Some`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    /// let mut x = None;
    ///
    /// {
    ///     let y: &mut u32 = x.get_or_insert(5);
    ///     assert_eq!(y, &5);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Some(7));
    /// ```
    fn get_or_insert(&mut self, value: T) -> &mut T
        where
            T: Drop;

    /// Inserts the default value into the option if it is [`None`], then
    /// returns a mutable reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let mut x = None;
    ///
    /// {
    ///     let y: &mut u32 = x.get_or_insert_default();
    ///     assert_eq!(y, &0);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Some(7));
    /// ```
    fn get_or_insert_default(&mut self) -> &mut T
        where
            T: Default;

    /// Inserts a value computed from `f` into the option if it is [`None`],
    /// then returns a mutable reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    /// let mut x = None;
    ///
    /// {
    ///     let y: &mut u32 = x.get_or_insert_with(|| 5);
    ///     assert_eq!(y, &5);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Some(7));
    /// ```
    fn get_or_insert_with<F>(&mut self, f: F) -> &mut T
        where
            F: FnOnce() -> T,
            F: Drop;

    /////////////////////////////////////////////////////////////////////////
    // Misc
    /////////////////////////////////////////////////////////////////////////

    /// Takes the value out of the option, leaving a [`None`] in its place.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    /// let mut x = Some(2);
    /// let y = x.take();
    /// assert_eq!(x, None);
    /// assert_eq!(y, Some(2));
    ///
    /// let mut x: Option<u32> = None;
    /// let y = x.take();
    /// assert_eq!(x, None);
    /// assert_eq!(y, None);
    /// ```
    fn take(&mut self) -> Option<T>;

    /// Returns `true` if the option is a [`Some`] value containing the given value.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let x: Option<u32> = Some(2);
    /// assert_eq!(x.contains(&2), true);
    ///
    /// let x: Option<u32> = Some(3);
    /// assert_eq!(x.contains(&2), false);
    ///
    /// let x: Option<u32> = None;
    /// assert_eq!(x.contains(&2), false);
    /// ```
    #[must_use]
    fn contains<U>(&self, x: &U) -> bool
        where
            U: PartialEq<T>;

    /// Zips `self` with another `Option`.
    ///
    /// If `self` is `Some(s)` and `other` is `Some(o)`, this method returns `Some((s, o))`.
    /// Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let x = Some(1);
    /// let y = Some("hi");
    /// let z = None::<u8>;
    ///
    /// assert_eq!(x.zip(y), Some((1, "hi")));
    /// assert_eq!(x.zip(z), None);
    /// ```
    fn zip<U>(self, other: Option<U>) -> Option<(T, U)>;

    /// Zips `self` and another `Option` with function `f`.
    ///
    /// If `self` is `Some(s)` and `other` is `Some(o)`, this method returns `Some(f(s, o))`.
    /// Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Point {
    ///     x: f64,
    ///     y: f64,
    /// }
    ///
    /// impl Point {
    ///     fn new(x: f64, y: f64) -> Self {
    ///         Self { x, y }
    ///     }
    /// }
    ///
    /// let x = Some(17.5);
    /// let y = Some(42.7);
    ///
    /// assert_eq!(x.zip_with(y, Point::new), Some(Point { x: 17.5, y: 42.7 }));
    /// assert_eq!(x.zip_with(None, Point::new), None);
    /// ```
    fn zip_with<U, F, R>(self, other: Option<U>, f: F) -> Option<R>
        where
            F: FnOnce(T, U) -> R;
}

impl<T> OptionsExtended<T> for Option<T> {
    /// Returns `true` if the option is a [`Some`] wrapping a value matching the predicate.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let x: Option<u32> = Some(2);
    /// assert_eq!(x.is_some_with(|&x| x > 1), true);
    ///
    /// let x: Option<u32> = Some(0);
    /// assert_eq!(x.is_some_with(|&x| x > 1), false);
    ///
    /// let x: Option<u32> = None;
    /// assert_eq!(x.is_some_with(|&x| x > 1), false);
    /// ```
    #[must_use]
    #[inline]
    fn is_some_with(&self, f: impl FnOnce(&T) -> bool) -> bool {
        matches!(self, Some(x) if f(x))
    }

    /// Calls the provided closure with a reference to the contained value (if [`Some`]).
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let v = vec![1, 2, 3, 4, 5];
    ///
    /// // prints "got: 4"
    /// let x: Option<&usize> = v.get(3).inspect(|x| println!("got: {}", x));
    ///
    /// // prints nothing
    /// let x: Option<&usize> = v.get(5).inspect(|x| println!("got: {}", x));
    /// ```
    #[inline]
    fn inspect<F>(self, f: F) -> Self
        where
            F: FnOnce(&T),
    {
        if let Some(ref x) = self {
            f(x);
        }

        self
    }

    /////////////////////////////////////////////////////////////////////////
    // Iterator constructors
    /////////////////////////////////////////////////////////////////////////

    /// Returns an iterator over the possibly contained value.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let x = Some(4);
    /// assert_eq!(x.iter().next(), Some(&4));
    ///
    /// let x: Option<u32> = None;
    /// assert_eq!(x.iter().next(), None);
    /// ```
    #[inline]
    fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: Item { opt: self.as_ref() },
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Entry-like operations to insert a value and return a reference
    /////////////////////////////////////////////////////////////////////////

    /// Inserts `value` into the option, then returns a mutable reference to it.
    ///
    /// If the option already contains a value, the old value is dropped.
    ///
    /// See also [`Option::get_or_insert`], which doesn't update the value if
    /// the option already contains [`Some`].
    ///
    /// # Example
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let mut opt = None;
    /// let val = opt.insert(1);
    /// assert_eq!(*val, 1);
    /// assert_eq!(opt.unwrap(), 1);
    /// let val = opt.insert(2);
    /// assert_eq!(*val, 2);
    /// *val = 3;
    /// assert_eq!(opt.unwrap(), 3);
    /// ```
    #[must_use = "if you intended to set a value, consider assignment instead"]
    #[inline]
    fn insert(&mut self, value: T) -> &mut T
        where
            T: Drop,
    {
        *self = Some(value);

        // SAFETY: the code above just filled the option
        unsafe { self.as_mut().unwrap_unchecked() }
    }

    /// Inserts `value` into the option if it is [`None`], then
    /// returns a mutable reference to the contained value.
    ///
    /// See also [`Option::insert`], which updates the value even if
    /// the option already contains [`Some`].
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let mut x = None;
    ///
    /// {
    ///     let y: &mut u32 = x.get_or_insert(5);
    ///     assert_eq!(y, &5);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Some(7));
    /// ```
    #[inline]
    fn get_or_insert(&mut self, value: T) -> &mut T
        where
            T: Drop,
    {
        if let None = *self {
            *self = Some(value);
        }

        // SAFETY: a `None` variant for `self` would have been replaced by a `Some`
        // variant in the code above.
        unsafe { self.as_mut().unwrap_unchecked() }
    }

    /// Inserts the default value into the option if it is [`None`], then
    /// returns a mutable reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let mut x = None;
    ///
    /// {
    ///     let y: &mut u32 = x.get_or_insert_default();
    ///     assert_eq!(y, &0);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Some(7));
    /// ```
    #[inline]
    fn get_or_insert_default(&mut self) -> &mut T
        where
            T: Default,
    {
        fn default<T: Default>() -> T {
            T::default()
        }

        self.get_or_insert_with(default)
    }

    /// Inserts a value computed from `f` into the option if it is [`None`],
    /// then returns a mutable reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let mut x = None;
    ///
    /// {
    ///     let y: &mut u32 = x.get_or_insert_with(|| 5);
    ///     assert_eq!(y, &5);
    ///
    ///     *y = 7;
    /// }
    ///
    /// assert_eq!(x, Some(7));
    /// ```
    #[inline]
    fn get_or_insert_with<F>(&mut self, f: F) -> &mut T
        where
            F: FnOnce() -> T,
            F: Drop,
    {
        if let None = *self {
            // the compiler isn't smart enough to know that we are not dropping a `T`
            // here and wants us to ensure `T` can be dropped at compile time.
            mem::forget(mem::replace(self, Some(f())))
        }

        // SAFETY: a `None` variant for `self` would have been replaced by a `Some`
        // variant in the code above.
        unsafe { self.as_mut().unwrap_unchecked() }
    }

    /////////////////////////////////////////////////////////////////////////
    // Misc
    /////////////////////////////////////////////////////////////////////////

    /// Takes the value out of the option, leaving a [`None`] in its place.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let mut x = Some(2);
    /// let y = x.take();
    /// assert_eq!(x, None);
    /// assert_eq!(y, Some(2));
    ///
    /// let mut x: Option<u32> = None;
    /// let y = x.take();
    /// assert_eq!(x, None);
    /// assert_eq!(y, None);
    /// ```
    #[inline]
    fn take(&mut self) -> Option<T> {
        // FIXME replace `mem::replace` by `mem::take` when the latter is const ready
        mem::replace(self, None)
    }

    /// Returns `true` if the option is a [`Some`] value containing the given value.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let x: Option<u32> = Some(2);
    /// assert_eq!(x.contains(&2), true);
    ///
    /// let x: Option<u32> = Some(3);
    /// assert_eq!(x.contains(&2), false);
    ///
    /// let x: Option<u32> = None;
    /// assert_eq!(x.contains(&2), false);
    /// ```
    #[must_use]
    #[inline]
    fn contains<U>(&self, x: &U) -> bool
        where
            U: PartialEq<T>,
    {
        match self {
            Some(y) => x.eq(y),
            None => false,
        }
    }

    /// Zips `self` with another `Option`.
    ///
    /// If `self` is `Some(s)` and `other` is `Some(o)`, this method returns `Some((s, o))`.
    /// Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// let x = Some(1);
    /// let y = Some("hi");
    /// let z = None::<u8>;
    ///
    /// assert_eq!(x.zip(y), Some((1, "hi")));
    /// assert_eq!(x.zip(z), None);
    /// ```
    fn zip<U>(self, other: Option<U>) -> Option<(T, U)> {
        match (self, other) {
            (Some(a), Some(b)) => Some((a, b)),
            _ => None,
        }
    }

    /// Zips `self` and another `Option` with function `f`.
    ///
    /// If `self` is `Some(s)` and `other` is `Some(o)`, this method returns `Some(f(s, o))`.
    /// Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use railsgun::OptionsExtended;
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Point {
    ///     x: f64,
    ///     y: f64,
    /// }
    ///
    /// impl Point {
    ///     fn new(x: f64, y: f64) -> Self {
    ///         Self { x, y }
    ///     }
    /// }
    ///
    /// let x = Some(17.5);
    /// let y = Some(42.7);
    ///
    /// assert_eq!(x.zip_with(y, Point::new), Some(Point { x: 17.5, y: 42.7 }));
    /// assert_eq!(x.zip_with(None, Point::new), None);
    /// ```
    fn zip_with<U, F, R>(self, other: Option<U>, f: F) -> Option<R>
        where
            F: FnOnce(T, U) -> R,
    {
        match (self, other) {
            (Some(a), Some(b)) => Some(f(a, b)),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
struct Item<A> {
    opt: Option<A>,
}

impl<A> Iterator for Item<A> {
    type Item = A;

    #[inline]
    fn next(&mut self) -> Option<A> {
        self.opt.take()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.opt {
            Some(_) => (1, Some(1)),
            None => (0, Some(0)),
        }
    }
}

impl<A> DoubleEndedIterator for Item<A> {
    #[inline]
    fn next_back(&mut self) -> Option<A> {
        self.opt.take()
    }
}

impl<A> ExactSizeIterator for Item<A> {}
impl<A> FusedIterator for Item<A> {}

/// An iterator over a reference to the [`Some`] variant of an [`Option`].
///
/// The iterator yields one value if the [`Option`] is a [`Some`], otherwise none.
///
/// This `struct` is created by the [`Option::iter`] function.

#[derive(Debug)]
pub struct Iter<'a, A: 'a> {
    inner: Item<&'a A>,
}

impl<'a, A> Iterator for Iter<'a, A> {
    type Item = &'a A;

    #[inline]
    fn next(&mut self) -> Option<&'a A> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, A> DoubleEndedIterator for Iter<'a, A> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a A> {
        self.inner.next_back()
    }
}

impl<A> ExactSizeIterator for Iter<'_, A> {}

impl<A> FusedIterator for Iter<'_, A> {}

impl<A> Clone for Iter<'_, A> {
    #[inline]
    fn clone(&self) -> Self {
        Iter {
            inner: self.inner.clone(),
        }
    }
}

/// An iterator over a mutable reference to the [`Some`] variant of an [`Option`].
///
/// The iterator yields one value if the [`Option`] is a [`Some`], otherwise none.
///
/// This `struct` is created by the [`Option::iter_mut`] function.

#[derive(Debug)]
pub struct IterMut<'a, A: 'a> {
    inner: Item<&'a mut A>,
}

impl<'a, A> Iterator for IterMut<'a, A> {
    type Item = &'a mut A;

    #[inline]
    fn next(&mut self) -> Option<&'a mut A> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, A> DoubleEndedIterator for IterMut<'a, A> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut A> {
        self.inner.next_back()
    }
}

impl<A> ExactSizeIterator for IterMut<'_, A> {}

impl<A> FusedIterator for IterMut<'_, A> {}


pub trait IntoOption
    where
        Self: Sized,
{
    fn into_option(self) -> Option<Self>;
}

impl<T> IntoOption for Vec<T> {
    fn into_option(self) -> Option<Self> {
        if self.is_empty() {
            None
        } else {
            Some(self)
        }
    }
}
