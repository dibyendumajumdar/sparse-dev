#ifdef __CHECKER__
#define __bitwise	__attribute__((bitwise))
#define __force		__attribute__((force))
#else
#define __bitwise
#define __force
#endif

typedef enum __bitwise foobar {
        FOO = 0,
        BAR = 1,
} fb_t;

static void foo(void)
{
	fb_t v = BAR;
}

/*
 * check-name: enum-restricted
 * check-known-to-fail
 */
