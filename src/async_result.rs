use core::future::Future;

use core::iter::FusedIterator;
use core::ops::{Deref, DerefMut};
use core::{convert, fmt, hint};

use AsyncResult::{Err, Ok};

/// # AsyncResult
/// The async AsyncResult is a AsyncResult implementation done for allowing the execution of async functions
/// within `map`, `map_err`, `and_then` etc. Similar to the regular `AsyncResult`.
/// The concept is to allow for fully async rails in Rust and execute code without using the `?` and breaking the paradigm of rails.

pub enum AsyncResult<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> AsyncResult<T, E> {
    /////////////////////////////////////////////////////////////////////////
    // Querying the contained values
    /////////////////////////////////////////////////////////////////////////

    /// Returns `true` if the AsyncResult is [`Ok`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<i32, &str> = Ok(-3);
    /// assert_eq!(x.is_ok(), true);
    ///
    /// let x: AsyncResult<i32, &str> = Err("Some error message");
    /// assert_eq!(x.is_ok(), false);
    /// ```
    pub const fn is_ok(&self) -> bool {
        match self {
            Ok(_) => true,
            Err(_) => false,
        }
    }

    /// Returns `true` if the AsyncResult is [`Err`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<i32, &str> = Ok(-3);
    /// assert_eq!(x.is_err(), false);
    ///
    /// let x: AsyncResult<i32, &str> = Err("Some error message");
    /// assert_eq!(x.is_err(), true);
    /// ```
    pub const fn is_err(&self) -> bool {
        match self {
            Ok(_) => false,
            Err(_) => true,
        }
    }

    /// Returns `true` if the AsyncResult is an [`Ok`] value containing the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(option_result_contains)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// assert_eq!(x.contains(&2), true);
    ///
    /// let x: AsyncResult<u32, &str> = Ok(3);
    /// assert_eq!(x.contains(&2), false);
    ///
    /// let x: AsyncResult<u32, &str> = Err("Some error message");
    /// assert_eq!(x.contains(&2), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn contains<U>(&self, x: &U) -> bool
    where
        U: PartialEq<T>,
    {
        match self {
            Ok(y) => x == y,
            Err(_) => false,
        }
    }

    /// Returns `true` if the AsyncResult is an [`Err`] value containing the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_contains_err)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// assert_eq!(x.contains_err(&"Some error message"), false);
    ///
    /// let x: AsyncResult<u32, &str> = Err("Some error message");
    /// assert_eq!(x.contains_err(&"Some error message"), true);
    ///
    /// let x: AsyncResult<u32, &str> = Err("Some other error message");
    /// assert_eq!(x.contains_err(&"Some error message"), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn contains_err<F>(&self, f: &F) -> bool
    where
        F: PartialEq<E>,
    {
        match self {
            Ok(_) => false,
            Err(e) => f == e,
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Adapter for each variant
    /////////////////////////////////////////////////////////////////////////

    /// Converts from `AsyncResult<T, E>` to [`Option<T>`].
    ///
    /// Converts `self` into an [`Option<T>`], consuming `self`,
    /// and discarding the error, if any.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// assert_eq!(x.ok(), Some(2));
    ///
    /// let x: AsyncResult<u32, &str> = Err("Nothing here");
    /// assert_eq!(x.ok(), None);
    /// ```
    #[inline]
    pub fn ok(self) -> Option<T> {
        match self {
            Ok(x) => Some(x),
            Err(_) => None,
        }
    }

    /// Converts from `AsyncResult<T, E>` to [`Option<E>`].
    ///
    /// Converts `self` into an [`Option<E>`], consuming `self`,
    /// and discarding the success value, if any.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// assert_eq!(x.err(), None);
    ///
    /// let x: AsyncResult<u32, &str> = Err("Nothing here");
    /// assert_eq!(x.err(), Some("Nothing here"));
    /// ```
    #[inline]
    pub fn err(self) -> Option<E> {
        match self {
            Ok(_) => None,
            Err(x) => Some(x),
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Adapter for working with references
    /////////////////////////////////////////////////////////////////////////

    /// Converts from `&Result<T, E>` to `AsyncResult<&T, &E>`.
    ///
    /// Produces a new `AsyncResult`, containing a reference
    /// into the original, leaving the original in place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// assert_eq!(x.as_ref(), Ok(&2));
    ///
    /// let x: AsyncResult<u32, &str> = Err("Error");
    /// assert_eq!(x.as_ref(), Err(&"Error"));
    /// ```
    #[inline]
    pub const fn as_ref(&self) -> AsyncResult<&T, &E> {
        match *self {
            Ok(ref x) => Ok(x),
            Err(ref x) => Err(x),
        }
    }

    /// Converts from `&mut AsyncResult<T, E>` to `AsyncResult<&mut T, &mut E>`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// fn mutate(r: &mut AsyncResult<i32, i32>) {
    ///     match r.as_mut() {
    ///         Ok(v) => *v = 42,
    ///         Err(e) => *e = 0,
    ///     }
    /// }
    ///
    /// let mut x: AsyncResult<i32, i32> = Ok(2);
    /// mutate(&mut x);
    /// assert_eq!(x.unwrap(), 42);
    ///
    /// let mut x: AsyncResult<i32, i32> = Err(13);
    /// mutate(&mut x);
    /// assert_eq!(x.unwrap_err(), 0);
    /// ```
    #[inline]
    pub fn as_mut(&mut self) -> AsyncResult<&mut T, &mut E> {
        match *self {
            Ok(ref mut x) => Ok(x),
            Err(ref mut x) => Err(x),
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Transforming contained values
    /////////////////////////////////////////////////////////////////////////

    /// Maps a `AsyncResult<T, E>` to `AsyncResult<U, E>` by applying a function to a
    /// contained [`Ok`] value, leaving an [`Err`] value untouched.
    ///
    /// This function can be used to compose the AsyncResults of two functions.
    ///
    /// # Examples
    ///
    /// Print the numbers on each line of a string multiplied by two.
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    /// use railgun::IntoAsync;
    ///
    /// let line = "1\n2\n3\n4\n";
    ///
    /// for num in line.lines() {
    ///     match num.parse::<i32>().into_async().async_map(|i| async {i * 2}).await {
    ///         Ok(n) => println!("{}", n),
    ///         Err(..) => {}
    ///     }
    /// }
    /// ```
    ///
    /// > TODO: Example needs improvement!
    #[inline]
    pub async fn async_map<U, UO: Future<Output = U>, F: FnOnce(T) -> UO>(
        self,
        op: F,
    ) -> AsyncResult<U, E> {
        match self {
            Ok(t) => Ok(op(t).await),
            Err(e) => Err(e),
        }
    }

    /// Maps a `AsyncResult<T, E>` to `AsyncResult<U, E>` by applying a function to a
    /// contained [`Ok`] value, leaving an [`Err`] value untouched.
    ///
    /// This function can be used to compose the AsyncResults of two functions.
    ///
    /// # Examples
    ///
    /// Print the numbers on each line of a string multiplied by two.
    ///
    /// ```
    /// use railgun::IntoAsync;
    ///
    /// let line = "1\n2\n3\n4\n";
    ///
    /// for num in line.lines() {
    ///     match num.parse::<i32>().into_async().map(|i| i * 2) {
    ///         Ok(n) => println!("{}", n),
    ///         Err(..) => {}
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn map<U, F: FnOnce(T) -> U>(self, op: F) -> AsyncResult<U, E> {
        match self {
            Ok(t) => Ok(op(t)),
            Err(e) => Err(e),
        }
    }

    /// Applies a function to the contained value (if [`Ok`]),
    /// or returns the provided default (if [`Err`]).
    ///
    /// Arguments passed to `map_or` are eagerly evaluated; if you are passing
    /// the AsyncResult of a function call, it is recommended to use [`map_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`map_or_else`]: AsyncResult::map_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<_, &str> = Ok("foo");
    /// assert_eq!(x.async_map_or(42, |v| async{v.len()}).await, 3);
    ///
    /// let x: AsyncResult<&str, _> = Err("bar");
    /// assert_eq!(x.async_map_or(42, |v| async{v.len()}).await, 42);
    /// ```
    #[inline]
    pub async fn async_map_or<U, UO: Future<Output = U>, F: FnOnce(T) -> UO>(
        self,
        default: U,
        f: F,
    ) -> U {
        match self {
            Ok(t) => f(t).await,
            Err(_) => default,
        }
    }

    /// Applies a function to the contained value (if [`Ok`]),
    /// or returns the provided default (if [`Err`]).
    ///
    /// Arguments passed to `map_or` are eagerly evaluated; if you are passing
    /// the AsyncResult of a function call, it is recommended to use [`map_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`map_or_else`]: AsyncResult::map_or_else
    ///
    /// # Examples
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<_, &str> = Ok("foo");
    /// assert_eq!(x.map_or(42, |v| v.len()), 3);
    ///
    /// let x: AsyncResult<&str, _> = Err("bar");
    /// assert_eq!(x.map_or(42, |v| v.len()), 42);
    /// ```
    #[inline]
    pub fn map_or<U, F: FnOnce(T) -> U>(self, default: U, f: F) -> U {
        match self {
            Ok(t) => f(t),
            Err(_) => default,
        }
    }

    /// Maps a `AsyncResult<T, E>` to `U` by applying a function to a
    /// contained [`Ok`] value, or a fallback function to a
    /// contained [`Err`] value.
    ///
    /// This function can be used to unpack a successful AsyncResult
    /// while handling an error.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let k = 21;
    ///
    /// let x : AsyncResult<_, &str> = Ok("foo");
    /// assert_eq!(x.async_map_or_else(|e| async {k * 2}, |v| async{v.len()}).await, 3);
    ///
    /// let x : AsyncResult<&str, _> = Err("bar");
    /// assert_eq!(x.async_map_or_else(|e| async{ k * 2}, |v| async{v.len()}).await, 42);
    /// ```
    #[inline]
    pub async fn async_map_or_else<
        U,
        UO: Future<Output = U>,
        D: FnOnce(E) -> UO,
        F: FnOnce(T) -> UO,
    >(
        self,
        default: D,
        f: F,
    ) -> U {
        match self {
            Ok(t) => f(t).await,
            Err(e) => default(e).await,
        }
    }

    /// Maps a `AsyncResult<T, E>` to `U` by applying a function to a
    /// contained [`Ok`] value, or a fallback function to a
    /// contained [`Err`] value.
    ///
    /// This function can be used to unpack a successful AsyncResult
    /// while handling an error.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let k = 21;
    ///
    /// let x : AsyncResult<_, &str> = Ok("foo");
    /// assert_eq!(x.map_or_else(|e| k * 2, |v| v.len()), 3);
    ///
    /// let x : AsyncResult<&str, _> = Err("bar");
    /// assert_eq!(x.map_or_else(|e| k * 2, |v| v.len()), 42);
    /// ```
    #[inline]
    pub fn map_or_else<U, D: FnOnce(E) -> U, F: FnOnce(T) -> U>(self, default: D, f: F) -> U {
        match self {
            Ok(t) => f(t),
            Err(e) => default(e),
        }
    }

    /// Maps a `AsyncResult<T, E>` to `AsyncResult<T, F>` by applying a function to a
    /// contained [`Err`] value, leaving an [`Ok`] value untouched.
    ///
    /// This function can be used to pass through a successful AsyncResult while handling
    /// an error.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// async fn stringify(x: u32) -> String{ format!("error code: {}", x) }
    ///
    /// let x: AsyncResult<u32, u32> = Ok(2);
    /// assert_eq!(x.async_map_err(stringify).await, Ok(2));
    ///
    /// let x: AsyncResult<u32, u32> = Err(13);
    /// assert_eq!(x.async_map_err(stringify).await, Err("error code: 13".to_string()));
    /// ```
    #[inline]
    pub async fn async_map_err<F, FO: Future<Output = F>, O: FnOnce(E) -> FO>(
        self,
        op: O,
    ) -> AsyncResult<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op(e).await),
        }
    }

    /// Maps a `AsyncResult<T, E>` to `AsyncResult<T, F>` by applying a function to a
    /// contained [`Err`] value, leaving an [`Ok`] value untouched.
    ///
    /// This function can be used to pass through a successful AsyncResult while handling
    /// an error.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// fn stringify(x: u32) -> String { format!("error code: {}", x) }
    ///
    /// let x: AsyncResult<u32, u32> = Ok(2);
    /// assert_eq!(x.map_err(stringify), Ok(2));
    ///
    /// let x: AsyncResult<u32, u32> = Err(13);
    /// assert_eq!(x.map_err(stringify), Err("error code: 13".to_string()));
    /// ```
    #[inline]
    pub fn map_err<F, O: FnOnce(E) -> F>(self, op: O) -> AsyncResult<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op(e)),
        }
    }

    /////////////////////////////////////////////////////////////////////////
    // Iterator constructors
    /////////////////////////////////////////////////////////////////////////

    /// Returns an iterator over the possibly contained value.
    ///
    /// The iterator yields one value if the AsyncResult is [`AsyncResult::Ok`], otherwise none.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(7);
    /// assert_eq!(x.iter().next(), Some(&7));
    ///
    /// let x: AsyncResult<u32, &str> = Err("nothing!");
    /// assert_eq!(x.iter().next(), None);
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.as_ref().ok(),
        }
    }

    /// Returns a mutable iterator over the possibly contained value.
    ///
    /// The iterator yields one value if the AsyncResult is [`AsyncResult::Ok`], otherwise none.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let mut x: AsyncResult<u32, &str> = Ok(7);
    /// match x.iter_mut().next() {
    ///     Some(v) => *v = 40,
    ///     None => {},
    /// }
    /// assert_eq!(x, Ok(40));
    ///
    /// let mut x: AsyncResult<u32, &str> = Err("nothing!");
    /// assert_eq!(x.iter_mut().next(), None);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            inner: self.as_mut().ok(),
        }
    }

    ////////////////////////////////////////////////////////////////////////
    // Boolean operations on the values, eager and lazy
    /////////////////////////////////////////////////////////////////////////

    /// Returns `res` if the AsyncResult is [`Ok`], otherwise returns the [`Err`] value of `self`.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// let y: AsyncResult<&str, &str> = Err("late error");
    /// assert_eq!(x.and(y), Err("late error"));
    ///
    /// let x: AsyncResult<u32, &str> = Err("early error");
    /// let y: AsyncResult<&str, &str> = Ok("foo");
    /// assert_eq!(x.and(y), Err("early error"));
    ///
    /// let x: AsyncResult<u32, &str> = Err("not a 2");
    /// let y: AsyncResult<&str, &str> = Err("late error");
    /// assert_eq!(x.and(y), Err("not a 2"));
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// let y: AsyncResult<&str, &str> = Ok("different AsyncResult type");
    /// assert_eq!(x.and(y), Ok("different AsyncResult type"));
    /// ```
    #[inline]
    pub fn and<U>(self, res: AsyncResult<U, E>) -> AsyncResult<U, E> {
        match self {
            Ok(_) => res,
            Err(e) => Err(e),
        }
    }

    /// Calls `op` if the AsyncResult is [`Ok`], otherwise returns the [`Err`] value of `self`.
    ///
    ///
    /// This function can be used for control flow based on `AsyncResult` values.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// async fn sq(x: u32) -> AsyncResult<u32, u32> { Ok(x * x) }
    /// async fn err(x: u32) -> AsyncResult<u32, u32> { Err(x) }
    ///
    /// assert_eq!(Ok(2).async_and_then(sq).await.async_and_then(sq).await, Ok(16));
    /// assert_eq!(Ok(2).async_and_then(sq).await.async_and_then(err).await, Err(4));
    /// assert_eq!(Ok(2).async_and_then(err).await.async_and_then(sq).await, Err(2));
    /// assert_eq!(Err(3).async_and_then(sq).await.async_and_then(sq).await, Err(3));
    /// ```
    #[inline]
    pub async fn async_and_then<U, OUT: Future<Output = AsyncResult<U, E>>, F: FnOnce(T) -> OUT>(
        self,
        op: F,
    ) -> AsyncResult<U, E> {
        match self {
            Ok(t) => op(t).await,
            Err(e) => Err(e),
        }
    }

    /// Calls `op` if the AsyncResult is [`Ok`], otherwise returns the [`Err`] value of `self`.
    ///
    ///
    /// This function can be used for control flow based on `AsyncResult` values.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// fn sq(x: u32) -> AsyncResult<u32, u32> { Ok(x * x) }
    /// fn err(x: u32) -> AsyncResult<u32, u32> { Err(x) }
    ///
    /// assert_eq!(Ok(2).and_then(sq).and_then(sq), Ok(16));
    /// assert_eq!(Ok(2).and_then(sq).and_then(err), Err(4));
    /// assert_eq!(Ok(2).and_then(err).and_then(sq), Err(2));
    /// assert_eq!(Err(3).and_then(sq).and_then(sq), Err(3));
    /// ```
    #[inline]
    pub fn and_then<U, F: FnOnce(T) -> AsyncResult<U, E>>(self, op: F) -> AsyncResult<U, E> {
        match self {
            Ok(t) => op(t),
            Err(e) => Err(e),
        }
    }

    /// Returns `res` if the AsyncResult is [`Err`], otherwise returns the [`Ok`] value of `self`.
    ///
    /// Arguments passed to `or` are eagerly evaluated; if you are passing the
    /// AsyncResult of a function call, it is recommended to use [`or_else`], which is
    /// lazily evaluated.
    ///
    /// [`or_else`]: AsyncResult::or_else
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// let y: AsyncResult<u32, &str> = Err("late error");
    /// assert_eq!(x.or(y), Ok(2));
    ///
    /// let x: AsyncResult<u32, &str> = Err("early error");
    /// let y: AsyncResult<u32, &str> = Ok(2);
    /// assert_eq!(x.or(y), Ok(2));
    ///
    /// let x: AsyncResult<u32, &str> = Err("not a 2");
    /// let y: AsyncResult<u32, &str> = Err("late error");
    /// assert_eq!(x.or(y), Err("late error"));
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// let y: AsyncResult<u32, &str> = Ok(100);
    /// assert_eq!(x.or(y), Ok(2));
    /// ```
    #[inline]
    pub fn or<F>(self, res: AsyncResult<T, F>) -> AsyncResult<T, F> {
        match self {
            Ok(v) => Ok(v),
            Err(_) => res,
        }
    }

    /// Calls `op` if the AsyncResult is [`Err`], otherwise returns the [`Ok`] value of `self`.
    ///
    /// This function can be used for control flow based on AsyncResult values.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// async fn sq(x: u32) -> AsyncResult<u32, u32> { Ok(x * x) }
    /// async fn err(x: u32) -> AsyncResult<u32, u32> { Err(x) }
    ///
    /// assert_eq!(Ok(2).async_or_else(sq).await.async_or_else(sq).await, Ok(2));
    /// assert_eq!(Ok(2).async_or_else(err).await.async_or_else(sq).await, Ok(2));
    /// assert_eq!(Err(3).async_or_else(sq).await.async_or_else(err).await, Ok(9));
    /// assert_eq!(Err(3).async_or_else(err).await.async_or_else(err).await, Err(3));
    /// ```
    #[inline]
    pub async fn async_or_else<F, OUT: Future<Output = AsyncResult<T, F>>, O: FnOnce(E) -> OUT>(
        self,
        op: O,
    ) -> AsyncResult<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => op(e).await,
        }
    }

    /// Calls `op` if the AsyncResult is [`Err`], otherwise returns the [`Ok`] value of `self`.
    ///
    /// This function can be used for control flow based on AsyncResult values.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// fn sq(x: u32) -> AsyncResult<u32, u32> { Ok(x * x) }
    /// fn err(x: u32) -> AsyncResult<u32, u32> { Err(x) }
    ///
    /// assert_eq!(Ok(2).or_else(sq).or_else(sq), Ok(2));
    /// assert_eq!(Ok(2).or_else(err).or_else(sq), Ok(2));
    /// assert_eq!(Err(3).or_else(sq).or_else(err), Ok(9));
    /// assert_eq!(Err(3).or_else(err).or_else(err), Err(3));
    /// ```
    #[inline]
    pub fn or_else<F, O: FnOnce(E) -> AsyncResult<T, F>>(self, op: O) -> AsyncResult<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => op(e),
        }
    }

    /// Returns the contained [`Ok`] value or a provided default.
    ///
    /// Arguments passed to `unwrap_or` are eagerly evaluated; if you are passing
    /// the AsyncResult of a function call, it is recommended to use [`unwrap_or_else`],
    /// which is lazily evaluated.
    ///
    /// [`unwrap_or_else`]: AsyncResult::unwrap_or_else
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let default = 2;
    /// let x: AsyncResult<u32, &str> = Ok(9);
    /// assert_eq!(x.unwrap_or(default), 9);
    ///
    /// let x: AsyncResult<u32, &str> = Err("error");
    /// assert_eq!(x.unwrap_or(default), default);
    /// ```
    #[inline]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Ok(t) => t,
            Err(_) => default,
        }
    }

    /// Returns the contained [`Ok`] value or computes it from a closure.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// async fn count(x: &str) -> usize { x.len() }
    ///
    /// assert_eq!(Ok(2).async_unwrap_or_else(count).await, 2);
    /// assert_eq!(Err("foo").async_unwrap_or_else(count).await, 3);
    /// ```
    #[inline]
    pub async fn async_unwrap_or_else<TO: Future<Output = T>, F: FnOnce(E) -> TO>(
        self,
        op: F,
    ) -> T {
        match self {
            Ok(t) => t,
            Err(e) => op(e).await,
        }
    }

    /// Returns the contained [`Ok`] value or computes it from a closure.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// fn count(x: &str) -> usize { x.len() }
    ///
    /// assert_eq!(Ok(2).unwrap_or_else(count), 2);
    /// assert_eq!(Err("foo").unwrap_or_else(count), 3);
    /// ```
    #[inline]
    pub fn unwrap_or_else<F: FnOnce(E) -> T>(self, op: F) -> T {
        match self {
            Ok(t) => t,
            Err(e) => op(e),
        }
    }

    /// Returns the contained [`Ok`] value, consuming the `self` value,
    /// without checking that the value is not an [`Err`].
    ///
    /// # Safety
    ///
    /// Calling this method on an [`Err`] is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(option_result_unwrap_unchecked)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// use std::future::Future;
    /// let x: dyn Future<Output = AsyncResult<u32, &str>> = Ok(2);
    /// assert_eq!(unsafe { x.unwrap_unchecked() }, 2);
    /// ```
    ///
    /// ```no_run
    /// #![feature(option_result_unwrap_unchecked)]
    /// use railgun::AsyncResult::{self, *};
    /// use std::future::Future;
    /// let x: dyn Future<Output = AsyncResult<u32, &str>> = Err("emergency failure");
    /// unsafe { x.unwrap_unchecked(); } // Undefined behavior!
    /// ```
    #[inline]
    #[track_caller]
    pub unsafe fn unwrap_unchecked(self) -> T {
        let sync_self = self;
        debug_assert!(sync_self.is_ok());
        match sync_self {
            Ok(t) => t,
            // SAFETY: the safety contract must be upheld by the caller.
            Err(_) => unsafe { hint::unreachable_unchecked() },
        }
    }

    /// Returns the contained [`Err`] value, consuming the `self` value,
    /// without checking that the value is not an [`Ok`].
    ///
    /// # Safety
    ///
    /// Calling this method on an [`Ok`] is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```no_run
    /// #![feature(option_result_unwrap_unchecked)]
    /// use railgun::AsyncResult::{self, *};
    /// use std::future::Future;
    ///
    /// let x: dyn Future<Output = AsyncResult<u32, &str>> = Ok(2);
    /// unsafe { x.unwrap_err_unchecked() }; // Undefined behavior!
    /// ```
    ///
    /// ```
    /// #![feature(option_result_unwrap_unchecked)]
    /// use railgun::AsyncResult::{self, *};
    /// use std::future::Future;
    ///
    /// let x: dyn Future<Output = AsyncResult<u32, &str>> = Err("emergency failure");
    /// assert_eq!(unsafe { x.unwrap_err_unchecked() }, "emergency failure");
    /// ```
    #[inline]
    #[track_caller]
    pub unsafe fn unwrap_err_unchecked(self) -> E {
        let sync_self = self;
        debug_assert!(sync_self.is_err());
        match sync_self {
            // SAFETY: the safety contract must be upheld by the caller.
            Ok(_) => unsafe { hint::unreachable_unchecked() },
            Err(e) => e,
        }
    }

    pub async fn async_merge<
        T1,
        U,
        FO: Future<Output = AsyncResult<U, E>>,
        F: FnOnce(T, T1) -> FO,
    >(
        self,
        res1: AsyncResult<T1, E>,
        op: F,
    ) -> AsyncResult<U, E> {
        match (self, res1) {
            (Ok(t), Ok(t1)) => op(t, t1).await,
            (Err(e), Ok(_t1)) => Err(e),
            (Ok(_t), Err(e1)) => Err(e1),
            (Err(e), Err(_e1)) => Err(e),
        }
    }

    pub async fn async_merge2<
        T1,
        T2,
        U,
        FO: Future<Output = AsyncResult<U, E>>,
        F: FnOnce(T, T1, T2) -> FO,
    >(
        self,
        res1: AsyncResult<T1, E>,
        res2: AsyncResult<T2, E>,
        op: F,
    ) -> AsyncResult<U, E> {
        self.async_merge(res1, |t, t1| async {
            Ok(t)
                .async_merge(res2, |t, t2| async { op(t, t1, t2).await })
                .await
        })
        .await
    }

    pub async fn async_merge3<
        T1,
        T2,
        T3,
        U,
        FO: Future<Output = AsyncResult<U, E>>,
        F: FnOnce(T, T1, T2, T3) -> FO,
    >(
        self,
        res1: AsyncResult<T1, E>,
        res2: AsyncResult<T2, E>,
        res3: AsyncResult<T3, E>,
        op: F,
    ) -> AsyncResult<U, E> {
        self.async_merge(res1, |t, t1| async {
            Ok(t)
                .async_merge(res2, |t, t2| async {
                    Ok(t).async_merge(res3, |t, t3| op(t, t1, t2, t3)).await
                })
                .await
        })
        .await
    }

    pub async fn async_merge4<
        T1,
        T2,
        T3,
        T4,
        U,
        FO: Future<Output = AsyncResult<U, E>>,
        F: FnOnce(T, T1, T2, T3, T4) -> FO,
    >(
        self,
        res1: AsyncResult<T1, E>,
        res2: AsyncResult<T2, E>,
        res3: AsyncResult<T3, E>,
        res4: AsyncResult<T4, E>,
        op: F,
    ) -> AsyncResult<U, E> {
        self.async_merge(res1, |t, t1| async {
            Ok(t)
                .async_merge(res2, |t, t2| async {
                    Ok(t)
                        .async_merge(res3, |t, t3| async {
                            Ok(t).async_merge(res4, |t, t4| op(t, t1, t2, t3, t4)).await
                        })
                        .await
                })
                .await
        })
        .await
    }

    pub fn merge<T1, U, F: FnOnce(T, T1) -> AsyncResult<U, E>>(
        self,
        res1: AsyncResult<T1, E>,
        op: F,
    ) -> AsyncResult<U, E> {
        match (self, res1) {
            (Ok(t), Ok(t1)) => op(t, t1),
            (Err(e), Ok(_t1)) => Err(e),
            (Ok(_t), Err(e1)) => Err(e1),
            (Err(e), Err(_e1)) => Err(e),
        }
    }

    pub fn merge2<T1, T2, U, F: FnOnce(T, T1, T2) -> AsyncResult<U, E>>(
        self,
        res1: AsyncResult<T1, E>,
        res2: AsyncResult<T2, E>,
        op: F,
    ) -> AsyncResult<U, E> {
        self.merge(res1, |t, t1| Ok(t).merge(res2, |t, t2| op(t, t1, t2)))
    }

    pub fn merge3<T1, T2, T3, U, F: FnOnce(T, T1, T2, T3) -> AsyncResult<U, E>>(
        self,
        res1: AsyncResult<T1, E>,
        res2: AsyncResult<T2, E>,
        res3: AsyncResult<T3, E>,
        op: F,
    ) -> AsyncResult<U, E> {
        self.merge(res1, |t, t1| {
            Ok(t).merge(res2, |t, t2| Ok(t).merge(res3, |t, t3| op(t, t1, t2, t3)))
        })
    }

    pub fn merge4<T1, T2, T3, T4, U, F: FnOnce(T, T1, T2, T3, T4) -> AsyncResult<U, E>>(
        self,
        res1: AsyncResult<T1, E>,
        res2: AsyncResult<T2, E>,
        res3: AsyncResult<T3, E>,
        res4: AsyncResult<T4, E>,
        op: F,
    ) -> AsyncResult<U, E> {
        self.merge(res1, |t, t1| {
            Ok(t).merge(res2, |t, t2| {
                Ok(t).merge(res3, |t, t3| {
                    Ok(t).merge(res4, |t, t4| op(t, t1, t2, t3, t4))
                })
            })
        })
    }
}

impl<T, E> From<Result<T, E>> for AsyncResult<T, E> {
    fn from(res: Result<T, E>) -> Self {
        match res {
            Result::Ok(t) => Ok(t),
            Result::Err(e) => Err(e),
        }
    }
}

impl<T, E> From<AsyncResult<T, E>> for Result<T, E> {
    fn from(ares: AsyncResult<T, E>) -> Self {
        match ares {
            Ok(t) => Result::Ok(t),
            Err(e) => Result::Err(e),
        }
    }
}

pub trait IntoAsync<T>: Sized {
    fn into_async(self) -> T;
}

impl<T, E> IntoAsync<AsyncResult<T, E>> for Result<T, E> {
    fn into_async(self) -> AsyncResult<T, E> {
        AsyncResult::from(self)
    }
}

pub trait IntoSync<T>: Sized {
    fn into_sync(self) -> T;
}

impl<T, E> IntoSync<Result<T, E>> for AsyncResult<T, E> {
    fn into_sync(self) -> Result<T, E> {
        Result::from(self)
    }
}

impl<T: Copy, E> AsyncResult<&T, E> {
    /// Maps a `AsyncResult<&T, E>` to a `AsyncResult<T, E>` by copying the contents of the
    /// `Ok` part.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_copied)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let val = 12;
    /// let x: AsyncResult<&i32, i32> = Ok(&val);
    /// assert_eq!(x, Ok(&12));
    /// let copied = x.copied();
    /// assert_eq!(copied, Ok(12));
    /// ```
    pub fn copied(self) -> AsyncResult<T, E> {
        self.map(|&t| t)
    }
}

impl<T: Copy, E> AsyncResult<&mut T, E> {
    /// Maps a `AsyncResult<&mut T, E>` to a `AsyncResult<T, E>` by copying the contents of the
    /// `Ok` part.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_copied)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let mut val = 12;
    /// let x: AsyncResult<&mut i32, i32> = Ok(&mut val);
    /// assert_eq!(x, Ok(&mut 12));
    /// let copied = x.copied();
    /// assert_eq!(copied, Ok(12));
    /// ```
    pub fn copied(self) -> AsyncResult<T, E> {
        self.map(|&mut t| t)
    }
}

impl<T: Clone, E> AsyncResult<&T, E> {
    /// Maps a `AsyncResult<&T, E>` to a `AsyncResult<T, E>` by cloning the contents of the
    /// `Ok` part.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_cloned)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let val = 12;
    /// let x: AsyncResult<&i32, i32> = Ok(&val);
    /// assert_eq!(x, Ok(&12));
    /// let cloned = x.cloned();
    /// assert_eq!(cloned, Ok(12));
    /// ```
    pub fn cloned(self) -> AsyncResult<T, E> {
        self.map(|t| t.clone())
    }
}

impl<T: Clone, E> AsyncResult<&mut T, E> {
    /// Maps a `AsyncResult<&mut T, E>` to a `AsyncResult<T, E>` by cloning the contents of the
    /// `Ok` part.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_cloned)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let mut val = 12;
    /// let x: AsyncResult<&mut i32, i32> = Ok(&mut val);
    /// assert_eq!(x, Ok(&mut 12));
    /// let cloned = x.cloned();
    /// assert_eq!(cloned, Ok(12));
    /// ```
    pub fn cloned(self) -> AsyncResult<T, E> {
        self.map(|t| t.clone())
    }
}

impl<T, E: fmt::Debug> AsyncResult<T, E> {
    /// Returns the contained [`Ok`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is an [`Err`], with a panic message including the
    /// passed message, and the content of the [`Err`].
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```should_panic
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Err("emergency failure");
    /// x.expect("Testing expect"); // panics with `Testing expect: emergency failure`
    /// ```
    #[inline]
    #[track_caller]
    pub fn expect(self, msg: &str) -> T {
        match self {
            Ok(t) => t,
            Err(e) => unwrap_failed(msg, &e),
        }
    }

    /// Returns the contained [`Ok`] value, consuming the `self` value.
    ///
    /// Because this function may panic, its use is generally discouraged.
    /// Instead, prefer to use pattern matching and handle the [`Err`]
    /// case explicitly, or call [`unwrap_or`], [`unwrap_or_else`], or
    /// [`unwrap_or_default`].
    ///
    /// [`unwrap_or`]: AsyncResult::unwrap_or
    /// [`unwrap_or_else`]: AsyncResult::unwrap_or_else
    /// [`unwrap_or_default`]: AsyncResult::unwrap_or_default
    ///
    /// # Panics
    ///
    /// Panics if the value is an [`Err`], with a panic message provided by the
    /// [`Err`]'s value.
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// use railgun::AsyncResult::{self, *};
    ///
    /// assert_eq!(x.unwrap(), 2);
    /// ```
    ///
    /// ```should_panic
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Err("emergency failure");
    /// x.unwrap(); // panics with `emergency failure`
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            Err(e) => unwrap_failed("called `AsyncResult::unwrap()` on an `Err` value", &e),
        }
    }
}

impl<T: fmt::Debug, E> AsyncResult<T, E> {
    /// Returns the contained [`Err`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is an [`Ok`], with a panic message including the
    /// passed message, and the content of the [`Ok`].
    ///
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```should_panic
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(10);
    /// x.expect_err("Testing expect_err"); // panics with `Testing expect_err: 10`
    /// ```
    #[inline]
    #[track_caller]
    pub fn expect_err(self, msg: &str) -> E {
        match self {
            Ok(t) => unwrap_failed(msg, &t),
            Err(e) => e,
        }
    }

    /// Returns the contained [`Err`] value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is an [`Ok`], with a custom panic message provided
    /// by the [`Ok`]'s value.
    ///
    /// # Examples
    ///
    /// ```should_panic
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(2);
    /// x.unwrap_err(); // panics with `2`
    /// ```
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Err("emergency failure");
    /// assert_eq!(x.unwrap_err(), "emergency failure");
    /// ```
    #[inline]
    #[track_caller]
    pub fn unwrap_err(self) -> E {
        match self {
            Ok(t) => unwrap_failed("called `AsyncResult::unwrap_err()` on an `Ok` value", &t),
            Err(e) => e,
        }
    }
}

impl<T: Default, E> AsyncResult<T, E> {
    /// Returns the contained [`Ok`] value or a default
    ///
    /// Consumes the `self` argument then, if [`Ok`], returns the contained
    /// value, otherwise if [`Err`], returns the default value for that
    /// type.
    ///
    /// # Examples
    ///
    /// Converts a string to an integer, turning poorly-formed strings
    /// into 0 (the default value for integers). [`parse`] converts
    /// a string to any other type that implements [`FromStr`], returning an
    /// [`Err`] on error.
    ///
    /// ```
    /// let good_year_from_input = "1909";
    /// let bad_year_from_input = "190blarg";
    /// let good_year = good_year_from_input.parse().unwrap_or_default();
    /// let bad_year = bad_year_from_input.parse().unwrap_or_default();
    ///
    /// assert_eq!(1909, good_year);
    /// assert_eq!(0, bad_year);
    /// ```
    ///
    /// [`parse`]: str::parse
    /// [`FromStr`]: crate::str::FromStr
    #[inline]
    pub fn unwrap_or_default(self) -> T {
        match self {
            Ok(x) => x,
            Err(_) => Default::default(),
        }
    }
}

impl<T: Deref, E> AsyncResult<T, E> {
    /// Converts from `AsyncResult<T, E>` (or `&Result<T, E>`) to `AsyncResult<&<T as Deref>::Target, &E>`.
    ///
    /// Coerces the [`Ok`] variant of the original [`AsyncResult`] via [`Deref`](crate::ops::Deref)
    /// and returns the new [`AsyncResult`].
    ///
    /// # Examples
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<String, u32> = Ok("hello".to_string());
    /// let y: AsyncResult<&str, &u32> = Ok("hello");
    /// assert_eq!(x.as_deref(), y);
    ///
    /// let x: AsyncResult<String, u32> = Err(42);
    /// let y: AsyncResult<&str, &u32> = Err(&42);
    /// assert_eq!(x.as_deref(), y);
    /// ```
    pub fn as_deref(&self) -> AsyncResult<&T::Target, &E> {
        self.as_ref().map(|t| t.deref())
    }
}

impl<T: DerefMut, E> AsyncResult<T, E> {
    /// Converts from `AsyncResult<T, E>` (or `&mut AsyncResult<T, E>`) to `AsyncResult<&mut <T as DerefMut>::Target, &mut E>`.
    ///
    /// Coerces the [`Ok`] variant of the original [`AsyncResult`] via [`DerefMut`](crate::ops::DerefMut)
    /// and returns the new [`AsyncResult`].
    ///
    /// # Examples
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let mut s = "HELLO".to_string();
    /// let mut x: AsyncResult<String, u32> = Ok("hello".to_string());
    /// let y: AsyncResult<&mut str, &mut u32> = Ok(&mut s);
    /// assert_eq!(x.as_deref_mut().map(|x| { x.make_ascii_uppercase(); x }), y);
    ///
    /// let mut i = 42;
    /// let mut x: AsyncResult<String, u32> = Err(42);
    /// let y: AsyncResult<&mut str, &mut u32> = Err(&mut i);
    /// assert_eq!(x.as_deref_mut().map(|x| { x.make_ascii_uppercase(); x }), y);
    /// ```
    pub fn as_deref_mut(&mut self) -> AsyncResult<&mut T::Target, &mut E> {
        self.as_mut().map(|t| t.deref_mut())
    }
}

impl<T, E> AsyncResult<Option<T>, E> {
    /// Transposes a `AsyncResult` of an `Option` into an `Option` of a `AsyncResult`.
    ///
    /// `Ok(None)` will be mapped to `None`.
    /// `Ok(Some(_))` and `Err(_)` will be mapped to `Some(Ok(_))` and `Some(Err(_))`.
    ///
    /// # Examples
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// struct SomeErr;
    ///
    /// let x: AsyncResult<Option<i32>, SomeErr> = Ok(Some(5));
    /// let y: Option<AsyncResult<i32, SomeErr>> = Some(Ok(5));
    /// assert_eq!(x.transpose(), y);
    /// ```
    #[inline]
    pub fn transpose(self) -> Option<AsyncResult<T, E>> {
        match self {
            Ok(Some(x)) => Some(Ok(x)),
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        }
    }
}

impl<T, E> AsyncResult<AsyncResult<T, E>, E> {
    /// Converts from `AsyncResult<Result<T, E>, E>` to `AsyncResult<T, E>`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// #![feature(result_flattening)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<AsyncResult<&'static str, u32>, u32> = Ok(Ok("hello"));
    /// assert_eq!(Ok("hello"), x.flatten());
    ///
    /// let x: AsyncResult<AsyncResult<&'static str, u32>, u32> = Ok(Err(6));
    /// assert_eq!(Err(6), x.flatten());
    ///
    /// let x: AsyncResult<AsyncResult<&'static str, u32>, u32> = Err(6);
    /// assert_eq!(Err(6), x.flatten());
    /// ```
    ///
    /// Flattening only removes one level of nesting at a time:
    ///
    /// ```
    /// #![feature(result_flattening)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<AsyncResult<AsyncResult<&'static str, u32>, u32>, u32> = Ok(Ok(Ok("hello")));
    /// assert_eq!(Ok(Ok("hello")), x.flatten());
    /// assert_eq!(Ok("hello"), x.flatten().flatten());
    /// ```
    #[inline]
    pub fn flatten(self) -> AsyncResult<T, E> {
        self.and_then(convert::identity)
    }
}

impl<T> AsyncResult<T, T> {
    /// Returns the [`Ok`] value if `self` is `Ok`, and the [`Err`] value if
    /// `self` is `Err`.
    ///
    /// In other words, this function returns the value (the `T`) of a
    /// `AsyncResult<T, T>`, regardless of whether or not that AsyncResult is `Ok` or
    /// `Err`.
    ///
    /// This can be useful in conjunction with APIs such as
    /// [`Atomic*::compare_exchange`], or [`slice::binary_search`], but only in
    /// cases where you don't care if the AsyncResult was `Ok` or not.
    ///
    /// [`Atomic*::compare_exchange`]: crate::sync::atomic::AtomicBool::compare_exchange
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(result_into_ok_or_err)]
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let ok: AsyncResult<u32, u32> = Ok(3);
    /// let err: AsyncResult<u32, u32> = Err(4);
    ///
    /// assert_eq!(ok.into_ok_or_err(), 3);
    /// assert_eq!(err.into_ok_or_err(), 4);
    /// ```
    #[inline]
    pub fn into_ok_or_err(self) -> T {
        match self {
            Ok(v) => v,
            Err(v) => v,
        }
    }
}

// This is a separate function to reduce the code size of the methods
#[inline(never)]
#[cold]
#[track_caller]
fn unwrap_failed(msg: &str, error: &dyn fmt::Debug) -> ! {
    panic!("{}: {:?}", msg, error)
}

/////////////////////////////////////////////////////////////////////////////
// Trait implementations
/////////////////////////////////////////////////////////////////////////////

impl<T: Clone, E: Clone> Clone for AsyncResult<T, E> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Ok(x) => Ok(x.clone()),
            Err(x) => Err(x.clone()),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        match (self, source) {
            (Ok(to), Ok(from)) => to.clone_from(from),
            (Err(to), Err(from)) => to.clone_from(from),
            (to, from) => *to = from.clone(),
        }
    }
}

impl<T, E> IntoIterator for AsyncResult<T, E> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Returns a consuming iterator over the possibly contained value.
    ///
    /// The iterator yields one value if the AsyncResult is [`AsyncResult::Ok`], otherwise none.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use railgun::AsyncResult::{self, *};
    ///
    /// let x: AsyncResult<u32, &str> = Ok(5);
    /// let v: Vec<u32> = x.into_iter().collect();
    /// assert_eq!(v, [5]);
    ///
    /// let x: AsyncResult<u32, &str> = Err("nothing!");
    /// let v: Vec<u32> = x.into_iter().collect();
    /// assert_eq!(v, []);
    /// ```
    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        IntoIter { inner: self.ok() }
    }
}

impl<'a, T, E> IntoIterator for &'a AsyncResult<T, E> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T, E> IntoIterator for &'a mut AsyncResult<T, E> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

/////////////////////////////////////////////////////////////////////////////
// The AsyncResult Iterators
/////////////////////////////////////////////////////////////////////////////

/// An iterator over a reference to the [`Ok`] variant of a [`AsyncResult`].
///
/// The iterator yields one value if the AsyncResult is [`Ok`], otherwise none.
///
/// Created by [`AsyncResult::iter`].
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    inner: Option<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        self.inner.take()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<T> FusedIterator for Iter<'_, T> {}

impl<T> Clone for Iter<'_, T> {
    #[inline]
    fn clone(&self) -> Self {
        Iter { inner: self.inner }
    }
}

/// An iterator over a mutable reference to the [`Ok`] variant of a [`AsyncResult`].
///
/// Created by [`AsyncResult::iter_mut`].
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    inner: Option<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        self.inner.take()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {}

impl<T> FusedIterator for IterMut<'_, T> {}

/// An iterator over the value in a [`Ok`] variant of a [`AsyncResult`].
///
/// The iterator yields one value if the AsyncResult is [`Ok`], otherwise none.
///
/// This struct is created by the [`into_iter`] method on
/// [`AsyncResult`] (provided by the [`IntoIterator`] trait).
///
/// [`into_iter`]: IntoIterator::into_iter
#[derive(Clone, Debug)]
pub struct IntoIter<T> {
    inner: Option<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.take()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> FusedIterator for IntoIter<T> {}
