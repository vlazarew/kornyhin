/*@
	axiomatic getValue {
		logic int *value{L}(int *ar, integer i);

		lemma get_value_l{L}: \forall integer i, int *ar;
			(ar == value(ar, i) || ar != value(ar, i));
	}

	predicate test1{L}(int *ar, integer i) =
		*value(ar, i) == 0;

	predicate test2{L}(int *ar, integer i) =
		test1(ar, i);
*/