
#include <malloc.h>
#include "map.h"

Key *generateKey(int a, int b) {
    Key *key = malloc(sizeof(Key));

    key->a = a;
    key->b = b;

    return key;
}

Value *generateValue(int c, int d) {
    Value *value = malloc(sizeof(Value));

    value->c = c;
    value->d = d;

    return value;
}

int main(int argc, char *argv[]) {
    int success;
    Map *map = malloc(sizeof(Map));
    success = initializeMap(map, 5);
    if (success != 0) {
        printf("Error in initializeMap(map, 5)");
        return -1;
    }

    Key *key = generateKey(1, 1);
    Value *value = generateValue(10, 10);
    success = addElement(map, key, value);
    if (success != 1) {
        printf("Error in addElement(map, key, value)");
        return -1;
    }

    Value *item = malloc(sizeof(Value));
    success = getElement(map, key, item);
    if (success != 1) {
        printf("Error in getElement(map, key, item)");
        return -1;
    }

    Key *fakeKey = generateKey(1, 2);
    success = getElement(map, fakeKey, item);
    if (success != 0) {
        printf("Error in getElement(map, fakeKey, item)");
        return -1;
    }

    key = generateKey(2, 1);
    value = generateValue(20, 10);
    success = addElement(map, key, value);
    if (success != 1) {
        printf("Error in addElement(map, key, value)");
        return -1;
    }

    success = addElement(map, key, value);
    if (success != 0) {
        printf("Error in addElement(map, key, value)");
        return -1;
    }

    success = removeElement(map, key, item);
    if (success != 1) {
        printf("Error in removeElement(map, key, item)");
        return -1;
    }

    success = removeElement(map, fakeKey, item);
    if (success != 0) {
        printf("Error in removeElement(map, fakeKey, item)");
        return -1;
    }

    printf("Success");
    return 0;
}