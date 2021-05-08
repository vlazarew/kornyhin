/*@
    requires \offset_min(s) == 0;
    requires \offset_max(s) == 0;
    ensures \base_addr(s) != \base_addr(\result);
*/
void* f(void *s) {
    void *u = malloc(10);
    //@ assert s == u || s != u;
    return u;
}