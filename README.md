# RailsGun
RailsGun or Railgun, call it how you want it.
This crate add a lot of small but usefull functionality to the existing
Rail paradigm in rust.

If you are used to use rails in rust, you know what its all about! If
its the first time you hear about it I would highly suggest you to read
the following [Railway Oriented Programming](https://fsharpforfunandprofit.com/rop/);
In short its a programming style that I have found over multiple project
and services to reduce the errors.

This crate supplies you with some extra missing tools and simplifications
as follows:

## tap, tap_err, tap_ref, tap_err_ref
This is a nice little trait that adds the ability to "tap" the contents.
This means that you can get a copy/clone of the original content that
you can use for analysis or other destructive operations without
actually touching the original.

> Note:
> `tap_ref` and `tap_err_ref` unfortunatly
> is just a reference so destructive actions should not be taken.

## merge, merge2, merge3, merge4

This is for merging multiple results. If you have worked with rails
before you have probably tried the following:

```rust
x.and_then(|var_x|  
    y.and_then(|var_y|
        z.and_then(|var_z|
            func_xyz(var_x, var_y, var_z)
        )
    )
)
```
This is a very ugly method of combining 3 results, you could
split it out in multiple functions, but at times that is very
excessive. Merge supplies you with a nice functionality for this.
```rust
x.merge2(y, z, |var_x, var_y, var_z| func_xyz(var_x, var_y, var_z)
```
As you can see this simplifies the rail significantly and makes
it more readable/maintainable.


## Trait BlockInPlaceResult
This is a trait that requires your system to currently be running
inside a Tokio thread as it requires multithreading. That said it adds some
interesting capabilities on top of the result.
If the following annoys you:

```rust
async fn my_async_fn() -> Result<&str, &str> {
    Ok("Something awesome")
}
my_async_fn.await.and_then(|t| println!("{}", t))
```
This allows you to cut corners by:
```rust
async fn my_async_fn() -> Result<&str, &str> {
    Ok("Something awesome")
}
my_async_fn.and_then(|t| println!("{}", t))
```
Please note this is using tokios `block_in_place` for execution

## AsyncResult
As the name describes, this is an `AsyncResult`. It has almost everything
that a `Result` has, and some other extra features.
This allows you to execute `async` functions and code inside your rail
by doing the following
```rust
async fn do_something(t: &str) -> AsyncResult<&str,&str> {
    t
}

x.and_then(|t| do_something(t)).await
    .and_then(|t| async move { t }).await;
```
Of course this is not the prettiest thing, but it allows the system to
keep to its rail and keep processing without moving in and out of the rails.

Of course this also comes with `From`/`Into` implementations for `Result`
and even a `into_async`/`into_sync` implementation that is more descriptive
when converting between `AsyncResult` and `Result`

# ToDo
There is a significant need for more documentation on the trait and others
as this library has been in my private stack for a long time and did get the
doc-care it needed.
1. tap needs doc
2. merge needs doc
3. Implement `BlockInPlace` for `AsyncResult`

Please open a ticket for more ideas!

# Contribution
Feel free to contribute to the project. Currently the project is hosted
on both [GitHub](https://github.com/nebula-technologies/Railgun) and
my private [GitLab](https://gitlab.nebula.technology/rust/railsgun).
The main repository is the GitLab repository where all of the pipelines
and all of my projects exists.

# License
The MIT License (MIT)

Copyright © 2021 <copyright holders>

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
