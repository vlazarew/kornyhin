#include <malloc.h>
#include "map.h"

int initializeMap(Map *map, int size) {
    map->capacity = size;

    Item *items = malloc(sizeof(Item) * size);
    map->items = items;
    return 0;
}

void finalizeMap(Map *map) {
    free(map);
}

int addElement(Map *map, Key *key, Value *value) {
    Item newItem;
    newItem.key = *key;
    newItem.value = *value;
    newItem.existent = 1;

    if (map->count == map->capacity) {
        return 0;
    }

    for (int i = 0; i < map->capacity; ++i) {
        Item tmp = map->items[i];
        if (tmp.key.a == newItem.key.a && tmp.key.b == newItem.key.b) {
            return 0;
        }
    }

    map->count++;
    map->items[map->count] = newItem;

    return 1;
}

int removeElement(Map *map, Key *key, Value *value) {

    for (int i = 0; i < map->capacity; ++i) {
        Item tmp = map->items[i];
        if (tmp.key.a == key->a && tmp.key.b == key->b) {
            if (value != nullptr) {
                value = &tmp.value;
            }

            free(tmp);
        }
    }
    return 0;
}

int getElement(Map *map, Key *key, Value *value) {

    for (int i = 0; i < map->capacity; ++i) {
        Item tmp = map->items[i];
        if (tmp.key.a == key->a && tmp.key.b == key->b) {
            value = &tmp.value;
            return 1;
        }
    }

    return 0;
}
