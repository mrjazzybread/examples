public void copy_array(int[] a1, int[] a2)
/*@ requires array_slice(a1, 0, a1.length, _) &*&
             [?frac]array_slice(a2, 0, a2.length, ?vs) &*&
             a1.length == a2.length; @*/
/*@ ensures [frac]array_slice(a2, 0, a2.length, vs) &*&
            array_slice(a1, 0, a1.length, vs); @*/

{
    for(int i = 0; i < a1.length; i = i + 1)
    /*@ invariant array_slice(a1, 0, i, take(i, vs)) &*&
       array_slice(a1, i, a1.length, _) &*&
       [frac]array_slice(a2, 0, a2.length, vs) &*&
       0 <= i &*& i <= a1.length &*& a1.length == a2.length; @*/
    {
	a1[i] = a2[i];
	//@ take_one_more(i, vs);
    }
}

/*@ predicate CopyThreadInv(CopyThread t;) =
      t.a1 |-> ?a1 &*& t.a2 |-> ?a2 &*&
      array_slice(a1, 0, a1.length, _) &*&
      [1/2]array_slice(a2, 0, a2.length, ?vs) &*&
      a1.length == a2.length;
@*/

class CopyThread implements Runnable {

    //@ predicate pre () = CopyThreadInv(this);
    //@ predicate post () = true;

    public int[] a1;
    public int[] a2;
    public int x;

    public CopyThread(int[] a1, int[] a2)
    /*@ requires array_slice(a1, 0, a1.length, _) &*&
                 [1/2]array_slice(a2, 0, a2.length, _) &*&
                 a1.length == a2.length;
    @*/
    //@ ensures pre();
     {
        this.a1 = a1;
        this.a2 = a2;
    }

    public void run()
    //@ requires pre();
    //@ ensures post();
    {
        copy_array(a1, a2);
        //@ close post();
    }
}

public void test()
//@ requires true;
//@ ensures true;
{
    int a1[] = new int[100];
    int a2[] = new int[100];
    int a3[] = new int[100];

    Thread t1 = new Thread(new CopyThread(a1, a3));
    Thread t2 = new Thread(new CopyThread(a2, a3));
    t1.start();
    t2.start();
}
