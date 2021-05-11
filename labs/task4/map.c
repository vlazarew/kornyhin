#include <malloc.h>
#include "map.h"

/*@
    predicate key_valid(Map *map, integer index) = map->items[index].key.a != 0 || map->items[index].key.b != 0;

    predicate value_valid(Map *map, integer index) = map->items[index].value.c != 0 || map->items[index].value.d != 0;

    predicate item_valid(Map *map, integer index) = map->items[index].existent == 1 && 
        key_valid(map, index) && value_valid(map, index);

    predicate items_valid(Map *map) = \forall integer i; 0 <= i <= map->count ==> item_valid(map, i);

    predicate map_valid(Map *map) = 0 <= map->count <= map->capacity &&
        \valid(map->items + (0 .. map->count - 1)) &&
        items_valid(map) &&
        (\forall integer i; map->count <= i < map->capacity ==> !map->items[i].existent);

    predicate full(Map *map) = range_existent(map, 0, map->count);

    predicate range_existent(Map *map, integer m, integer n) = \forall integer k; m <= k < n ==> map->items[k].existent == 1;

    predicate item_saved{L1, L2}(Map *map, integer k) = \at(map->items[k], L1) == \at(map->items[k], L2);
    predicate items_saved{L1, L2}(Map *map, integer m, integer n) = \forall integer k; m <= k < n ==> item_saved{L1, L2}(map, k);
*/

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
            items_saved{L1, L2}(map, begin, end) ==> count_saved_p{L1, L2}(map, begin, end);

    axiom count_existent: \forall Map *map, integer begin, end;
            (\forall integer k; begin <= k < end ==> !map->items[k].existent == 1) || count(map, begin, end) == 0;

    logic integer all_count(Map *map) = count(map, 0, map->capacity);
}

*/


/**
 * Создание пустого ассоциативного массива.
 * @param map - указатель на инициализируемый массив
 * @param size - масмальный размер массива (кол-во items в нем)
 * @return 0 - все ОК, -1 - фиаско
 */
/*@
    requires    \valid(map) && map_valid(map);
    ensures     \forall integer i; 0 <= i < size ==> map->items[i].existent == 0;
    ensures     \result == 0 <==> map->capacity == size && map->count == 0;
    ensures     size < 0 <==> \result == -1;
    ensures     size >= 0 && \valid(map) <==> \result == 0;

    allocates map->items;
    frees \nothing;
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

    for (int i = 0; i < size; i++) {
        map->items[i].existent = 0;
    }

    return 0;
}

/**
 * Освобождаем динамическую память из под map
 * @param map - указатель на ассоциативный массив
 */
void finalizeMap(Map *map) {
    free(map->items);
}

/**
 * Реализация хеш-функции
 * @param key - указатель на ключ
 * @return промежуточное значение для рассчета индекса
 */
/*@
    requires \valid(key);
    ensures \result >= 0;
    ensures key == \old(key);
*/
int hash(Key *key) {
    int result = key->a * 33 + key->b;
    return result >= 0 ? result : -result;
}

/*@
    requires    \valid(map) && map_valid(map);
    requires    0 <= index <= map->capacity;
    ensures     map == \old(map);
    ensures     hashValue == \old(hashValue);
    ensures     index == \old(index);
    ensures     -map->capacity <= \result <= map->capacity;
*/
int getCalculatedIndex(Map *map, int hashValue, int index) { return (hashValue + index) % map->capacity; }

/**
 * Добавление в ассоциативный массив отображения key -> value
 * @param map - указатель на заданный ассоциативный массив
 * @param key - указатель на ключ
 * @param value - указатель на значение
 * @return 1 - ОК, 0 - фиаско
 */
int addElement(Map *map, Key *key, Value *value) {
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
}


/**
 * Удаление сохраненного значения из ассоциативного массива
 * @param map - указатель на заданный ассоциативный массив
 * @param key - указатель на ключ
 * @param value - указатель на значение
 * @return 1 - ОК, 0 - фиаско
 */
/*@
    requires    \valid(map) && map_valid(map);
    requires    \valid(key) && (\forall integer i; 0 <= i < map->count ==> key_valid(map, i));
    requires    \forall integer i; 0 <= i < map->count ==> value_valid(map, i);
    ensures     \valid(map) && map_valid(map);
    ensures     \old(map->count) == map->count + 1;
    ensures     \old(map->capacity) == map->capacity;
    ensures     \forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && \old(map->items[i].existent) == 1 ==> map->items[i].existent == 0;
    ensures     \forall integer i; (map->items[i].key.a != key->a || map->items[i].key.b != key->b) ==> map->items[i].existent == \old(map->items[i].existent);
    ensures     \forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && \old(map->items[i].existent) == 1 ==> \result == 1;
    ensures     \forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && \old(map->items[i].existent) == 0 ==> \result == 0;
    ensures     \forall integer i; (map->items[i].key.a != key->a || map->items[i].key.b != key->b) ==> \result == 0;
    ensures     \valid(\old(value)) ==> 
                    (\forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && \result == 1 ==> 
                        value->c == \old(map->items[i].value.c) && value->d == \old(map->items[i].value.d));
    ensures     key == \old(key);

    allocates \nothing;
    frees \nothing;

    assigns map->count;
    assigns map->items[0..map->capacity - 1];    
    assigns *value;
 */
int removeElement(Map *map, Key *key, Value *value) {
    int hashValue = hash(key);

    for (int index = 0; index < map->capacity; index++) {
        int calcIndex = getCalculatedIndex(map, hashValue, index);
//        Item tempItem = map->items[calcIndex];

//        Если нашли занятую ячейку и ключ совпал
        if (map->items[calcIndex].existent == 1 &&
            map->items[calcIndex].key.a == key->a &&
            map->items[calcIndex].key.b == key->b) {

//            Помечаем как удаленную, уменьшаем счетчик в ассоц массиве
            map->items[calcIndex].existent = 0;
            map->count--;

//            Опционально запоминаем удаляемое значение
            if (value) {
                *value = map->items[calcIndex].value;
            }

            return 1;
        }
    }

//    Когда не нашли вообще когда
    return 0;
}

/**
 * Получение значения элемента по его ключу в ассоциативном массиве
 * @param map - указатель на заданный ассоциативный массив
 * @param key - указатель на ключ
 * @param value - указатель на значение
 * @return 1 - ОК, 0 - фиаско
 */
/*@
    requires    \valid(map) && map_valid(map);
    requires    \valid(key) && (\forall integer i; 0 <= i < map->count ==> key_valid(map, i));
    requires    \forall integer i; 0 <= i < map->count ==> value_valid(map, i);

    ensures     \valid(map) && map_valid(map);
    ensures     \old(map->count) == map->count;
    ensures     \old(map->capacity) == map->capacity;
    ensures     \forall integer i; \old(map->items[i].key.a) == map->items[i].key.a && \old(map->items[i].key.b) == map->items[i].key.b 
                    && \old(map->items[i].existent) == map->items[i].existent 
                    && \old(map->items[i].value.c) == map->items[i].value.c && \old(map->items[i].value.d) == map->items[i].value.d;
    ensures     \forall integer i; (map->items[i].key.a != key->a || map->items[i].key.b != key->b) ==> map->items[i].existent == \old(map->items[i].existent);
    ensures     \forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && map->items[i].existent == 1 ==> \result == 1;
    ensures     \forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && map->items[i].existent == 0 ==> \result == 0;
    ensures     \forall integer i; (map->items[i].key.a != key->a || map->items[i].key.b != key->b) ==> \result == 0;
    ensures     \valid(\old(value)) ==> 
                    (\forall integer i; map->items[i].key.a == key->a && map->items[i].key.b == key->b && \result == 1 ==> 
                        value->c == \old(map->items[i].value.c) && value->d == \old(map->items[i].value.d));
    ensures key == \old(key);

    assigns *value;
    allocates \nothing;
    frees \nothing;
 */
int getElement(Map *map, Key *key, Value *value) {
    int hashValue = hash(key);

    for (int index = 0; index < map->capacity; index++) {
        int calcIndex = getCalculatedIndex(map, hashValue, index);
//        Item tempItem = map->items[calcIndex];

        //        Если нашли занятую ячейку и ключ совпал
        if (map->items[calcIndex].existent == 1 &&
            map->items[calcIndex].key.a == key->a &&
            map->items[calcIndex].key.b == key->b) {
//            Возвращаем значение
            *value = map->items[calcIndex].value;
            return 1;
        }
    }

//    Когда вообще нет такого эл-та в мапе
    return 0;
}
