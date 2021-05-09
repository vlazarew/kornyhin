#include <malloc.h>
#include "map.h"

/**
 * Создание пустого ассоциативного массива.
 * @param map - указатель на инициализируемый массив
 * @param size - масмальный размер массива (кол-во items в нем)
 * @return 0 - все ОК, -1 - фиаско
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
int hash(Key *key) {
    int result = key->a * 33 + key->b;
    return result >= 0 ? result : -result;
}

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

//        Если вдруг найдана свободная ячейка, то это фиаско
        if (map->items[calcIndex].existent == 0) {
            return 0;
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
int getElement(Map *map, Key *key, Value *value) {
    int hashValue = hash(key);

    for (int index = 0; index < map->capacity; index++) {
        int calcIndex = getCalculatedIndex(map, hashValue, index);
//        Item tempItem = map->items[calcIndex];

        //        Если нашли занятую ячейку и ключ совпал
//        if (tempItem.state == BUSY &&
        if (map->items[calcIndex].existent == 1 &&
                map->items[calcIndex].key.a == key->a &&
                map->items[calcIndex].key.b == key->b) {
//            Возвращаем значение
            *value = map->items[calcIndex].value;
            return 1;
        }

//        Если наткнулись на свободную ячейку
//        if (tempItem.state == FREE) {
        if (map->items[calcIndex].existent == 0) {
            return 0;
        }
    }

//    Когда вообще нет такого эл-та в мапе
    return 0;
}
