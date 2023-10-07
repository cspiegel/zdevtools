ifeq ($(CC), gcc)
CFLAGS+=	-Wall -Wshadow -std=c99 -pedantic

else ifeq ($(CC), clang)
CFLAGS+=	-Wall -std=c99 -pedantic

else ifeq ($(CC), icc)
CFLAGS+=	-w2 -wd2259,2557,869,981 -std=c99

else ifeq ($(CC), suncc)
CFLAGS+=	-xc99=all -Xc

else ifeq ($(CC), opencc)
CFLAGS+=	-Wall -std=c99

endif
