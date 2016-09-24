#[cfg(test)]
#[allow(dead_code, unused_assignments, unused_variables)]
mod tests {

    // use std::cell::RefCell;

    struct My;                  // not Copiable by default

    #[test]
    fn liveness_and_fields() {
        let x = &mut (0, 1);
        // let x_i = &x;           // ok if no mutable borrows
        {
            // reborrow x to two disjoint subfields
            let y_i = &x.0;
            let z_i = &x.1;
            // let z = &mut x.1;   // error, unless the next line is removed
            let x_i = &x;   // ok
            // y_i and z(_i) are now live, but x isn't
        }
        // y and z go out of scope, so x is live again
        *x = (4, 2);
    }

    #[test]
    fn sound_drop() -> () {
        struct UnsafeDropper<'a>(&'a i32);
        // Uncomment this and below to produce an error
        // impl<'a> Drop for UnsafeDropper<'a> {
        //     fn drop(&mut self) {
        //         // might refer to self.0
        //     }
        // }
        // let (x, ud);            // error
        let x; let ud;          // ok
        x = 42;
        ud = UnsafeDropper(&x);
    }

    #[test]
    fn dumb_lifetime() {
        struct Foo;
        impl Foo {
            fn mutate_and_share(&mut self) -> &Self { &*self }
            fn share(&self) {}
        }

        let mut foo = Foo;
        // {                       // ok
            // let loan =          // error
            foo.mutate_and_share();
        // }
        foo.share();
    }

    #[test]
    fn explicit_lifetime() {
        fn foo<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32 {
            x
        }

        let x = 12;
        let z: &i32 = {
            let y = 42;
            foo(&y, &x);
            foo(&x, &y)
            // foo(&y, &x)         // error
        };
        assert_eq!(*z, 12);
    }

    fn swap_by_xor(x: &mut i32, y: &mut i32) {
        *x ^= *y;
        *y ^= *x;
        *x ^= *y;
    }

    #[test]
    #[should_panic]
    fn runtime_aliasing() {
        use std::cell::RefCell;
        let (x, y) = (RefCell::new(4), RefCell::new(2));
        swap_by_xor(&mut x.borrow_mut(), &mut x.borrow_mut()); // !
    }

    #[test]
    fn safe_aliasing() {
        // fn test_swap<T, F: Fn(T, T)>(swap: F) {
        {
            let (mut x, mut y) = (4, 2);
            {
                swap_by_xor(&mut x, &mut y);
                assert_eq!((x, y), (2, 4));
            }
            // {
            //     swap_by_xor(&mut x, &mut x);
            //     assert_eq!(x, 0); // error
            // }
            // {
            //     let mut x_mref = &mut x;
            //     swap_by_xor(x_mref, x_mref); // error
            //     swap_by_xor(x_mref, &mut x); // error
            // }
        }
    }

    #[test]
    fn move_vs_copy_assignment() {
        let m = My;
        let m2 = m;             // ok (m is moved)
        // let m3 = m;             // error (My is move-only)

        #[derive(Copy, Clone)]
        struct C;

        let c = C;
        let c2 = c;
        let c3 = c;             // ok (c was copied to c2)
    }
}
