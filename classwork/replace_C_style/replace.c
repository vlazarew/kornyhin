// ACSL - ansii C specification language. Язык спец. 1 - приминений много(тесты, верификация, оптимизации).
// ==> отсутсвуют некоторые специфичные вещи(например, отсутсвует модель памяти)
// синтаксис:
/*
    requires {size >= 0}
    requires {forall ind. 0 <= ind < size -> valid (shift arr ind) !mem block_sizes}
    ensures {forall ind. 0 <= ind < size /\ select (old !mem) (shift arr ind) = a -> select !mem (shift arr ind) = b}
    ensures {forall ind. 0 <= ind < size /\ select (old !mem) (shift arr ind) <> a -> select !mem (shift arr ind) = select (old !mem) (shift arr ind)}
    ensures {forall p: pointer 't. valid p !mem block_sizes /\ same_block p arr /\  not (arr.offset <= p.offset < (shift arr size).offset) 
            -> select !mem p = select (old !mem) p}
    ensures {forall p: pointer 't. valid p !mem block_sizes /\ not (same_block p arr) -> select !mem p = select (old !mem) p}

*/
/*@
    requires size >= 0;
    requires \valid(array + (0..size-1)); 
    ensures \forall integer i; 0 <= i < size && \old(array[i]) == a ==> array[i] == b;
    ensures \forall integer i; 0 <= i < size && \old(array[i]) != a ==> \old(array[i]) == array[i];
    assigns array[0..size-1];
*/
void replace(int *array, int size, int a, int b) {
    int *p = array;
    /*
        invariant { 0 <= (!p.offset - arr.offset) <= size }
        invariant { forall ind. 0 <= ind < !p.offset - arr.offset /\ select (at !mem 'Pre) (shift arr ind) = a -> select !mem (shift arr ind) = b }
        invariant { forall ind. 0 <= ind < !p.offset - arr.offset /\ select (at !mem 'Pre) (shift arr ind) <> a -> select !mem (shift arr ind) = select (at !mem 'Pre) (shift arr ind)}
        invariant { forall ind. !p.offset - arr.offset <= ind < size -> select !mem (shift arr ind) = select (at !mem 'Pre) (shift arr ind) }
        invariant { same_block !p arr}
        invariant {forall p: pointer 't. valid p !mem block_sizes /\ same_block p arr /\  not (arr.offset <= p.offset < (shift arr size).offset) 
            -> select !mem p = select (at !mem 'Pre) p}
        invariant {forall p: pointer 't. valid p !mem block_sizes /\ not (same_block p arr) -> select !mem p = select (at !mem 'Pre) p}
        variant { size - (!p.offset - arr.offset) }
        
    */
    /*@
        loop invariant 0 <= (p - array) <= size;
        loop invariant \forall integer ind; 0 <= ind < (p - array) && \at(array[ind],Pre) == a ==> array[ind] == b;
        loop invariant \forall integer ind; 0 <= ind < (p - array) && \at(array[ind],Pre) != a ==> array[ind] == \at(array[ind],Pre);
        loop invariant \forall integer ind; (p - array) <= ind < size ==> array[ind] == \at(array[ind],Pre);
        loop invariant \base_addr(p) == \base_addr(array);
        loop assigns array[0..size-1];
        loop variant size - (p - array);
    */
    while (p - array < size) {
        if (*p == a) {
            *p = b;
        }
        p++;
    }
}

// int main(int argc, int *argv[]) {
//     int k = 6;
//     replace(&k, 1, 6, 5);
//     assert(k == 5);
//     return 0;
// }

int main(int argc, int *argv[]) {
    int *k = malloc(sizeof(int));
    *k = 6;
    replace(k, 1, 6, 5);
    assert(*k == 5);
    free(k);
    return 0;
}