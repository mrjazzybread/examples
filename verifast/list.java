public interface List {
   //@ predicate List(list<int> elements);

    void add(int x);
    //@ requires List(?l1);
    //@ ensures List(append(l1, cons(x, nil)));

}

public class ArrayList implements List {
    int size;
    int[] arr;

    /*@ predicate List(list<int> elts) =
          arr |-> ?a &*& size |-> ?n &*&
	  a.length > 0 &*&
	  array_slice(a, 0, n, elts) &*&
	  array_slice(a, n, a.length, _); @*/

    private int[] resize (int[] arr)
    //@ requires array_slice(arr, 0, arr.length, ?l);
    /*@ ensures arr.length * 2 == result.length &*&
      array_slice(result, 0, arr.length, l) &*&
      array_slice(result, arr.length, arr.length * 2, _); @*/
    {
	int[] arr_new = new int[arr.length * 2];
	for(int i = 0; i < arr.length; i++)
            /*@ invariant arr.length * 2 == arr_new.length &*&
	        i <= arr.length &*&
	          array_slice(arr, 0, arr.length, l) &*&
		  array_slice(arr_new, 0, i, take(i, l)) &*&
		  array_slice(arr_new, i, arr_new.length, _); @*/
	    {
		arr_new[i] = arr[i];
		//@ take_one_more(i, l);
	    }
	return arr_new;
    }

    void add(int x)
    //@ requires List(?l);
    //@ ensures List(append(l, cons(x, nil)));
    {
        if(size == arr.length)
	  arr = resize(arr);
	arr[size] = x;
	size = size + 1;

    }
}
