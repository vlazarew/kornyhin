// ACSL - ansii C Specification Language
// Язык спецификаци один, применений много (тесты, верификация, оптимизация)

// => отсутствуют некоторые специфичные вещи (например отсутствует модель памяти)

// Запуск frama-c -av replace.c 

// Отмена Old при помощи at
// ensures \forall integer      i; 0 <= i < size  && \old(\at(array, Here)[i]) == a ==> array[i] == b 

/*@
    requires    size >= 0;
    requires    \forall integer i;  0 <= i < size ==> \valid(array + i);  
    ensures     \forall integer i;  0 <= i < size  && \old(\at(array, Here)[i]) == a ==> array[i] == b 
    ensures     \forall integer i;  0 <= i < size  && \old(\at(array, Here)[i]) != a ==> \old(array[i]) = array[i] 
    assigns     array[0..size - 1]; */
// */
void replace(int *array, int size, int a, int b) {
    int *p = array;
    /*@
        loop invariant  ...;
        loop variant    ...;
        loop assigns    array[0..size - 1];
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
