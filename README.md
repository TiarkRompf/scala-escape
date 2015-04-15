The Great Escape
================

First-class service is nice. But if everybody rides first class, it stops being fun.

This Scala compiler plug-in exposes a programming model to enforce a _no-escape_ policy for certain objects.

There are many potential uses:

- Effects: 
    Objects can serve as capabilities. But we must limit the scope of capabilities to retain control. Compare to Monads, which do not compose well. 
- Region based memory:
    Deallocate and/or reuse memory in a timely manner (note that we do not aim to do this for _all_ allocations, just for big chunks).
- Resource control:
    Ensure that resources such as file handles are properly closed.
- Staging:
    Scope extrusion. We must limit the scope of binders to guarantee well-typed generated code.
- Distributed systems:
    We do not want to serialize large data by accident (see Spores).


A High-Level Example
--------------------

If an expression has type `A @safe(x)` it will not leak symbol `x`.

If a function has type `A => B @safe(%)`, it will not leak its argument.
Think of this as a dependent function type `(x:A) => B @safe(x)`.

    // For exception handling, we would like to enforce that
    // exceptions can only be raised within a try/catch block.

    def trycatch(f: (Exception => Nothing) => Unit @safe(%)): Unit

    // The closure passed to trycatch may not leak its argument.

    trycatch { raise =>
      raise(new Exception)  // ok: raise cannot escape
    }

    // Inside a try block we can use `raise` in safe positions,
    // but not in unsafe ones, where it could be leaked.

    def safeMethod(f: () => Any): Int @safe(f)
    def unsafeMethod(f: () => Any): Int

    trycatch { raise =>
      safeMethod { () =>
        raise(new Exception)  // ok: closure is safe
      }
      unsafeMethod { () =>
        raise(new Exception)  // not ok
      }
    }

See the [test suite](library/src/test/scala/scala/tools/escape) for complete code.


Practical Restrictions
----------------------

Consider the following example:

    def map[A,B](xs: List[A])(f: A => B): List[B] @safe(f) = {
      val b = new Builder[B]
      xs foreach (x => b += f(x))
      b.result
    }

We are not leaking `f`, but we _are_ leaking objects returned
from calling `f`.

It is no problem to use `map` like this:

    map(xs) { x =>
      if (x > 0) x else raise(new Exception)
    }

But we need to be careful about cases where
we could transitively leak `raise`, e.g. as part of
another closure:

    map(xs) { x =>
      () => raise(new Exception)
    }

The design decision here is to disallow this case.

Extensions to _n-level_ safety are conceivable.


Rationale and Background
------------------------

The concept of higher-order and first-class language constructs goes hand in hand. In a higher-order language, many things are first-class: functions, mutable references, etc.

Being first-class means that there are no restrictions on how an object may be used. Functions can be passed to other functions as arguments and returned from other functions. First class reference cells may hold functions or other reference cells.

Lexical scope is central to most modern programming languages. First-class functions _close over_ their defining scope. Hence they are also called closures.

While programming with first-class objects is incredibly useful, it is sometimes _too_ powerful, and one loses some useful guarantees.

For example, in a language without closures, function calls follow a strict stack discipline. A local variable's lifetime ends when the function returns and its space can be reclaimed. Contrast this with higher-order languages, which allocate closure records on the heap. The lifetime of a variable may be indefinite if it is captured by a closure.

Binding the lifetime of (certain -- not all) objects is important. So maybe not all objects should be first class?

After all, we want first class to be an exclusive club, with tightly regulates access. 


Current Status
--------------

Early development and proof of concept. Do not expect too much, but feel free to contribute!
