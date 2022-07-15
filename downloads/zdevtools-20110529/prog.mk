%.o: %.c
	$(CC) -g $(OPT) $(CFLAGS) $(MACROS) -c $< -o $@

$(PROG): $(PROG).o
	$(CC) $(OPT) $< -o $@ $(LDADD)

clean:
	rm -f $(PROG) *.o
