use vstd::prelude::*;

verus! {
    // basic recursive expression
    fn exec_basic_recursive_expr(i: u64) -> (r: u64)
        ensures af(done(r == i))
        decreases i
    {
        if i == 0 { 0 } else { 1 + exec_basic_recursive_expr(i - 1) }
    }

    // basic recursive statement — counts down to 0, no observable output
    // The postcondition captures that the function terminates (trivially true for i == 0)
    fn exec_basic_recursive_stmt(i: u64)
        decreases i 
    {
        if i != 0 {
            exec_basic_recursive_stmt(i - 1);
        }
    }

    // basic while loop — i goes from 0 to 10
    fn exec_basic_while_loop() -> (i: u64)
        ensures af(done(i == 10))
    {
        let mut i = 0;
        while i < 10
            invariant i <= 10
            decreases 10 - i
        {
            i = i + 1;
        }
        assert(i == 10);
        i
    }

    // nested while — i reaches 10
    fn exec_nested_while_loop() -> (r: (u64, u64))
        ensures
            af(done(r.0 == 10)),
            af(done(r.1 <= 5)),
    {
        let mut i = 0;
        let mut j = 0;
        while i < 10 
            invariant 
                i <= 10,
                j <= 5
            decreases 10 - i
            {
                i = i + 1;
                while j < 5
                    invariant j <= 5
                    decreases 5 - j
                    {
                        j = j + 1;
                    }
            }
        (i, j)
    }

    // infinite loop with break — i reaches 10
    fn exec_basic_loop_break() -> (result: i8)
        ensures af(done(1 <= result && result <= 10))
    {
        let mut i: i8 = 0;
        loop
            invariant_except_break i <= 9
            invariant 0 <= i <= 10
            ensures 1 <= i
            decreases 10 - i
        {
            i = i + 1;
            if i == 10 {
                break;
            }
        }
        i
    }

    // for loop — n accumulates 3 per iteration for 10 iterations = 30
    fn exec_for_loop() -> (n: u64)
        ensures af(done(n == 30))
    {
        let mut n: u64 = 0;
        for x in iter: 0..10
            invariant n == iter.cur * 3,
        {
            n += 3;
        }
        n
    }

    fn exec_for_loop_2() -> (n: u64)
        ensures af(done(n == 30))
    {
        let mut n: u64 = 0;
        let mut end = 10;
        for x in iter: 0..end 
            invariant 
                n == iter.cur * 3,
                end == 10,
        {
            n += 3;
        }
        n
    }

    // recursive + while combo — terminates for all i <= 10
    #[verifier::loop_isolation(false)]
    fn exec_basic_recursive_stmt_basic_while_loop(mut i: u64)
        requires i <= 10,
        decreases i,
    {
        let ghost initial_i = i;
        while 0 < i && i <= 10
            invariant
                0 <= i <= 10,
                i <= initial_i,
            decreases i,
        {
            exec_basic_recursive_stmt_basic_while_loop(i - 1);
            i -= 1;
        }
    }
}