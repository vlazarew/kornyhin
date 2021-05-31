// #include <malloc.h>
// #include "map.h"

/*@ 

axiomatic ItemsCount{
    logic integer count{L}(Map *map, integer begin, integer end);

    axiom count_zero: \forall Map *map, integer begin, end; begin >= end ==> count(map, begin, end) == 0;

    axiom count_one: \forall Map *map, integer index; count(map, index, index + 1) == (map->items[index].existent == 1 ? 1 : 0);

    axiom count_split: \forall Map *map, integer begin, index, end; begin <= index <= end ==>
        count(map, begin, end) == count(map, begin, index) + count(map, index, end);

    predicate count_saved_p{L1, L2}(Map *map, integer begin, integer end) =
            count{L1}(map, begin, end) == count{L2}(map, begin, end);

    axiom count_saved{L1, L2}: \forall Map *map, integer begin, end;
            items_deleted{L1, L2}(map, begin, end) ==> count_saved_p{L1, L2}(map, begin, end);

    axiom count_existent: \forall Map *map, integer begin, end;
            (\forall integer k; begin <= k < end ==> !map->items[k].existent == 1) || count(map, begin, end) == 0;

    logic integer all_count(Map *map) = count(map, 0, map->capacity);
}
*/
// */

/*
    1. Структура может хранить лишь единственное отображение для конкретного ключа. Отображение представляется типом Item.
    2. Его поле existent может быть истиной (то есть равняться единице) или ложью (то есть равняться нулю).
    3. Поле items структуры Map представляет собой массив длины capacity.
    4. Поле count этой структуры определяет, сколько элементов данного массива имеет поле existent установленным в истину (единицу).
    5. При работе со структурой учитываются те и только те записи массива items, которые имеют булево поле existent установленным в истину (единицу).
        Никакие операции над структурой данных не должны приводить ее в такое состояние, чтобы после этого добавление одного отображения 
        увеличило количество отображений более, чем на 1. Иными словами, в структуре данных, все existent элементы массива должны означать 
        отображения из хэш-таблицы.
*/


/*@

    predicate into_int_range(integer value) = -2147483648 <= value <= 2147483647;


    predicate is_key_valid(Map *map, integer index) = (map->items[index].key.a != 0 && into_int_range(map->items[index].key.a)) 
                                                || (map->items[index].key.b != 0 && into_int_range(map->items[index].key.b));

    predicate is_value_valid(Map *map, integer index) = map->items[index].value.c != 0 || map->items[index].value.d != 0;

    predicate is_key_exists{L}(Map *map, Key *key) = \exists integer index; 0 <= index < map->capacity 
                                                            && is_item_exists(map, index) 
                                                            && map->items[index].key == *key;

    predicate is_item_exists(Map *map, integer index) = map->items[index].existent == 1 && 
        is_key_valid(map, index) && is_value_valid(map, index);

    predicate is_items_valid(Map *map) = \forall integer i; 0 <= i <= map->count ==> is_item_exists(map, i);

    predicate is_pair_exists{L}(Map *map, Key *key, Value *value) = \exists integer index; 0 <= index < map->capacity &&
                                                                            is_item_exists(map, index) &&
                                                                            map->items[index].key == *key &&
                                                                            map->items[index].value == *value;

    predicate full(Map *map) = range_existent(map, 0, map->count);

    predicate range_existent(Map *map, integer m, integer n) = \forall integer k; m <= k < n ==> map->items[k].existent == 1;

    predicate item_deleted{L1, L2}(Map *map, integer index) = \at(map->items[index], L1) == \at(map->items[index], L2);
    predicate items_deleted{L1, L2}(Map *map, integer begin, integer end) = \forall integer k; begin <= k < end ==> item_deleted{L1, L2}(map, k);

    // Условие №1
    predicate is_keys_unique(Map *map) = \forall integer index1, index2; 0 <= index1 < index2 < map->capacity && 
                                                                            map->items[index1].existent == 1 &&
                                                                            map->items[index2].existent == 1 
                                                                                ==> map->items[index1].key != map->items[index2].key;

    // Условие №2 
    predicate is_states_correct(Map *map) = \forall integer index; 0 <= map->capacity ==> 0 <= map->items[index].existent <= 1;

    // Условие №3
    predicate is_map_valid(Map *map) = 0 <= map->count <= map->capacity && \valid(map->items + (0 .. map->capacity - 1));
    
    // Условие №4
    predicate is_map_correct(Map *map) = is_keys_unique(map) && is_states_correct(map) &&
                                             all_count(map) == map->count && map->capacity > 0 &&
                                            (\forall integer i; map->count <= i < map->capacity ==> !map->items[i].existent) && 
                                            is_map_valid(map);

    // Условие №5
    predicate map_stability(Map *map) = \forall integer i, j; 0 <= i <= map->capacity && 
                                                        0 <= j <= map->capacity && 
                                                        i != j && is_item_exists(map, i) && is_item_exists(map, j) 
                                                                    ==> map->items[i].key != map->items[j].key;*/
// */


/**
 * Создание пустого ассоциативного массива.
 * @param map - указатель на инициализируемый массив
 * @param size - масмальный размер массива (кол-во items в нем)
 * @return 0 - все ОК, -1 - фиаско
 * 
 * Функция initializeMap() создаёт пустой ассоциативный массив              [1]
 * с заданным числом максимально хранимых элементов size,                   [2]
 * выделяя под него динамическую память.                                    [3]
 * На вход функции должен подаваться указатель на переменную-структуру,     [4]
 * функция должна проинициализировать эту структуру.                        [5]
 * В случае неуспеха, функция должна вернуть ненулевое число,               [6]
 * иначе функция должна вернуть 0.                                          [7]
 * 
 */
/*@
    requires    size > 0;                                                                          // [2]
    requires    \valid(map);                                                                       // [4]
    ensures     \result == 0 ==> is_map_valid(map);                                                // [3, 5, 7]
    ensures     \result == 0 ==> map->capacity == size;                                            // [2, 5, 7]
    ensures     \result == 0 ==> map->count == 0;                                                  // [5, 7]
    ensures     \result == 0 ==> \forall integer i; 0 <= i < size ==> map->items[i].existent == 0; // [1, 5, 7]
    ensures     \result != 0 ==> !is_map_valid(map);                                               // [6]

    allocates   map->items;
    frees       \nothing;
 */
int initializeMap(Map *map, int size) {
//    Проверка на дурака (зачем выделять память под ничего)
    if (size <= 0) {
        return -1;
    }

//    Выделение памяти непосредстсвенно
    map->items = malloc(size * sizeof(Item));

//    В случае, если память не выделилась
    if (!map->items) {
        return -1;
    }

//    Инициализация дефолтными значениями
    map->capacity = size;
    map->count = 0;

    /*@
        loop invariant 0 <= i <= size;
        loop invariant \forall integer index; 0 <= index < i ==> map->items[index].existent == 0;
        loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        map->items[i].existent = 0;
    }

    return 0;
}

/**
 * Освобождаем динамическую память из под map
 * @param map - указатель на ассоциативный массив
 */
/*void finalizeMap(Map *map) {
    free(map->items);
}*/

/**
 * Реализация хеш-функции
 * @param key - указатель на ключ
 * @return промежуточное значение для рассчета индекса
 */
/*@
    requires    \valid(key);
    ensures     0 <= \result <= 34 * (2147483647 + 1);
    ensures     key == \old(key);
    assigns     \nothing;*/
// */
long hash(Key *key) {
    long result = key->a;
    result *= 33;
    result += key->b;
    return result >= 0 ? result : -(result + 1);
}

/*@
    requires    \valid(map) && is_map_correct(map);
    requires    0 <= index <= map->capacity;
    requires    map->capacity > 0;
    requires    0 <= hashValue <= 34 * (2147483647 + 1);
    ensures     map == \old(map);
    ensures     \valid(map) && is_map_correct(map);
    ensures     hashValue == \old(hashValue);
    ensures     index == \old(index);
    ensures     0 <= \result < map->capacity;*/
// */
int getCalculatedIndex(Map *map, long hashValue, int index) { return (hashValue + index) % map->capacity; }

/**
 * Добавление в ассоциативный массив отображения key -> value
 * @param map - указатель на заданный ассоциативный массив
 * @param key - указатель на ключ
 * @param value - указатель на значение
 * @return 1 - ОК, 0 - фиаско
 */
/*int addElement(Map *map, Key *key, Value *value) {
//    Получение хеша от ключа
    int hashValue = hash(key);

    for (int index = 0; index < map->capacity; index++) {
        int calcIndex = getCalculatedIndex(map, hashValue, index);
//        Item *tempItem = &map->items[calcIndex];

// Хранить можем только единственное отображение
        if (map->items[calcIndex].existent == 1 && 
            map->items[calcIndex].key.a == key->a &&
            map->items[calcIndex].key.b == key->b){
                return 0;
            }

//        Если попали в незанятую ячейку
        if (map->items[calcIndex].existent != 1) {
//            Заполняем вводными данными
            map->items[calcIndex].key = *key;
            map->items[calcIndex].value = *value;
            map->items[calcIndex].existent = 1;
//            Отражаем добавление в count
            map->count++;
//            Well
            return 1;
        }
    }

//    Если мы здесь, то ни разу не попали в незанятую ячейку => нам не хватило места
    return 0;
}*/


/**
 * Удаление сохраненного значения из ассоциативного массива
 * @param map - указатель на заданный ассоциативный массив
 * @param key - указатель на ключ
 * @param value - указатель на значение
 * @return 1 - ОК, 0 - фиаско
 *
 *
 * Функция removeElement() удаляет сохранённое в ассоциативном массиве map значение по заданному ключу key (если оно там было). [1]
 * Функция не удаляет другие отображения, кроме отображения по заданному ключу,                                                 [2]
 * а также не добавляет новые отображения.                                                                                      [3]
 * Функция возвращает истину (единицу), если функция изменила ассоциативный массив,                                             [4]
 * ложь (ноль) в противном случае.                                                                                              [5]
 * В случае, если значение было удалено и при этом переданный указатель value был отличен от нулевого, 
 *  функция записывает значение, содержавшееся для заданного ключа, по данному указателю.                                       [6]
 * Функция имеет право изменять структуру ассоциативного массива, если это не отражается на содержащихся в нём парах.           [7]
 * Ничего другого функция не делает.                                                                                            [8]
 */
/*@
    requires    \valid(map) && is_map_correct(map);                                                     // [General]
    requires    \valid(key) && (\forall integer i; 0 <= i < map->count ==> is_key_valid(map, i));       // [General]
    requires    \forall integer i; 0 <= i < map->count ==> is_value_valid(map, i);                      // [General]

    ensures     *key == \old(*key);                                                                     // [8]
    ensures     \valid(\old(value)) && \result == 1 ==>                                                 // [4, 6]
                    (\forall integer i; map->items[i].key.a == key->a && 
                    map->items[i].key.b == key->b && \result == 1 ==> 
                        value->c == \old(map->items[i].value.c) && 
                        value->d == \old(map->items[i].value.d));

    ensures     \valid(map) && is_map_correct(map);                                                     // [7]
    ensures     \result == 1 ==> \old(map->count) == map->count + 1;                                    // [1, 2, 3]
    ensures     \result == 0 ==> \old(map->count) == map->count;                                        // [1]
    ensures     \old(map->capacity) == map->capacity;                                                   // [8]

    ensures     \result == 1 ==> is_key_exists(\old(map), key) && !is_key_exists(map, key);             // [4]
    ensures     \result == 1 ==> is_pair_exists(\old(map), key, \old(value)) &&                         // [4]
                                                     !is_pair_exists(map, key, value); 
    ensures     !is_key_exists(\old(map), key) ==> \result == 0;                                        // [5]
    ensures     map->count == 0 && 
                           \forall integer index; map->items[index].existent == 0 ==> \result == 0;     // [5]

    ensures     is_key_exists{Pre}(map, key) ==> \result == 1 &&                                        // [4, 5]
                    ((all_count(map) + 1) == all_count{Pre}(map)) && !is_pair_exists(map, key, value);

    allocates \nothing;                                                                                 // [8]
    frees \nothing;                                                                                     // [8]

    assigns map->count;                                                                                 // [8]
    assigns map->items[0..map->capacity - 1];                                                           // [8]
    assigns *value;                                                                                     // [6, 8]
 */
int removeElement(Map *map, Key *key, Value *value) {
    long hashValue = hash(key);
    /*@ assert 0 <= hashValue <= 34 * (2147483647 + 1);*/

    /*@
        loop invariant 0 <= index <= map->capacity;
        loop variant map->capacity - index;
    */
    for (int index = 0; index < map->capacity; index++) {
        /*@ assert is_map_correct(map);*/
        int calcIndex = getCalculatedIndex(map, hashValue, index);
//        Item tempItem = map->items[calcIndex];

        /*@ assert 0 <= calcIndex < map->capacity;*/
//        Если нашли занятую ячейку и ключ совпал
        if (map->items[calcIndex].existent == 1 &&
            map->items[calcIndex].key.a == key->a &&
            map->items[calcIndex].key.b == key->b) {

//            Помечаем как удаленную, уменьшаем счетчик в ассоц массиве
            /*@ assert is_key_exists(map, key);*/
            /*@ assert is_item_exists(map, calcIndex);*/
            map->items[calcIndex].existent = 0;
            map->count--;

            /*@ assert (all_count(map) - 1) == all_count{Pre}(map);*/
            /*@ assert 0 <= map->count <= map->capacity;*/
//            Опционально запоминаем удаляемое значение
            if (value) {
                *value = map->items[calcIndex].value;
            }

            return 1;
        }
    }

    /*@ assert !is_key_exists(map, key);*/
	/*@ assert !is_pair_exists(map, key, value);*/
//    Когда не нашли вообще когда
    return 0;
}

/**
 * Получение значения элемента по его ключу в ассоциативном массиве
 * @param map - указатель на заданный ассоциативный массив
 * @param key - указатель на ключ
 * @param value - указатель на значение
 * @return 1 - ОК, 0 - фиаско
 * 
 * Функция getElement() возвращает по указателю value сохранённое в ассоциативном массиве map значение для заданного ключа key      [1]
 * и возвращает истину (единицу), если заданный ассоциативный массив имеет отображения для заданного ключа.                         [2]
 * В случае, если значение по заданному ключу не содержится в отображении, возвращается ложь (ноль) и ничего другого не происходит. [3]
 * Функция не меняет ассоциативный массив и переданный ключ.                                                                        [4]
 * Ничего другого функция не делает.                                                                                                [5]
 *
 */
/*@
    requires    \valid(map) && is_map_correct(map) ;                                                    // [General]
    requires    \valid(key) && (\forall integer i; 0 <= i < map->count ==> is_key_valid(map, i));       // [General]
    requires    \valid(value) && (\forall integer i; 0 <= i < map->count ==> is_value_valid(map, i));   // [General]

    ensures     \valid(map) && is_map_correct(map);                                                     // [4, 5]
    ensures     \old(map->count) == map->count;                                                         // [4, 5]
    ensures     \old(map->capacity) == map->capacity;                                                   // [4, 5]
    ensures     \forall integer i; \old(map->items[i].key.a) == map->items[i].key.a                     // [4, 5]
                    && \old(map->items[i].key.b) == map->items[i].key.b 
                    && \old(map->items[i].existent) == map->items[i].existent 
                    && \old(map->items[i].value.c) == map->items[i].value.c 
                    && \old(map->items[i].value.d) == map->items[i].value.d;
    ensures     key == \old(key);                                                                       // [4, 5]
    ensures     is_key_exists(map, key) && is_pair_exists(map, key, value) ==> \result == 1;            // [1, 2]
    ensures     !is_key_exists(map, key) ==> \result == 0 && value == \old(value);                      // [3]

    // ensures     \forall integer i; (map->items[i].key.a != key->a || map->items[i].key.b != key->b) ==> map->items[i].existent == \old(map->items[i].existent);
    // ensures     \forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && map->items[i].existent == 1 ==> \result == 1;
    // ensures     \forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && map->items[i].existent == 0 ==> \result == 0;
    // ensures     \forall integer i; (map->items[i].key.a != key->a || map->items[i].key.b != key->b) ==> \result == 0;
    // ensures     \valid(\old(value)) ==> 
    //                 (\forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && \result == 1 ==> 
    //                     value->c == \old(map->items[i].value.c) && value->d == \old(map->items[i].value.d));

    assigns     *value;                                                                                 // [1]
    allocates   \nothing;                                                                               // [4, 5]
    frees       \nothing;                                                                               // [4, 5]
 */
int getElement(Map *map, Key *key, Value *value) {
    long hashValue = hash(key);

    /*@ assert 0 <= hashValue <= 34 * (2147483647 + 1);*/

    /*@
        loop invariant 0 <= index <= map->capacity;
        loop variant map->capacity - index;
    */
    for (int index = 0; index < map->capacity; index++) {
        /*@ assert is_map_correct(map);*/
        int calcIndex = getCalculatedIndex(map, hashValue, index);
//        Item tempItem = map->items[calcIndex];

        /*@ assert 0 <= calcIndex < map->capacity;*/
        //        Если нашли занятую ячейку и ключ совпал
        if (map->items[calcIndex].existent == 1 &&
            map->items[calcIndex].key.a == key->a &&
            map->items[calcIndex].key.b == key->b) {
            /*@ assert is_item_exists(map, calcIndex);*/
//            Возвращаем значение
            *value = map->items[calcIndex].value;
            return 1;
        }
    }

    /*@ assert !is_key_exists(map, key);*/
//    Когда вообще нет такого эл-та в мапе
    return 0;
}
