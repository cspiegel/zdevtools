/*-
 * Copyright (c) 2010-2011 Chris Spiegel
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <errno.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

#define err(...)	do { fprintf(stderr, __VA_ARGS__); fprintf(stderr, ": %s\n", strerror(errno)); exit(1); } while(0)
#define errx(...)	do { fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); exit(1); } while(0)

static int dumphex = 0;
static int dumpstring = 0;
static int print_width = 8;
static char newlinechar = '\n';

static uint8_t *memory;
static size_t memory_size;
static uint16_t abbr_table;
static uint32_t R_O, S_O;
static uint32_t main_routine;

static int ignore_errors = 0;

static uint8_t atable[26 * 3] =
{
  /* A0 */
  'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
  'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',

  /* A1 */
  'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
  'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',

  /* A2 */
  0x0, 0xd, '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '.',
  ',', '!', '?', '_', '#', '\'','"', '/', '\\','-', ':', '(', ')',
};


static int nargs;
static long args[8];

static uint8_t BYTE(uint32_t addr)
{
  if(addr >= memory_size) errx("byte %lx is out of bounds", (unsigned long)addr);

  return memory[addr];
}

static uint16_t WORD(uint32_t addr)
{
  if(addr + 1 >= memory_size) errx("word %lx is out of bounds", (unsigned long)addr);

  return memory[addr] << 8 | memory[addr + 1];
}

static int zversion;

#define F_STORE		0x001
#define F_BRANCH	0x002
#define F_STRING	0x004
#define F_PSTRING	0x008
#define F_CALL1		0x010
#define F_CALL2		0x020
#define F_CALL3		0x040
#define F_JUMP		0x080
#define F_INDIRECT	0x100
#define F_RETURN	0x200

struct opcode
{
  enum count { ZERO, ONE, TWO, VAR, EXT } count;
  int number;

  const char *name;
  int flags;
};

struct instruction
{
  unsigned long addr, nextaddr;

  const struct opcode *opcode;

  int nargs;
  long args[8];

  int invbranch;
  unsigned long branchto;

  long storeto;

  char *string;

  struct instruction *next;
};

static struct instruction *instructions;
static size_t ninst;

static void add_instruction(struct instruction inst)
{
  struct instruction *new;

  new = malloc(sizeof *new);
  if(new == NULL) err("malloc");

  *new = inst;
  new->next = instructions;
  instructions = new;

  ninst++;
}

static void append(struct instruction **list, struct instruction **tail, struct instruction *node)
{
  node->next = NULL;

  if(*list == NULL)
  {
    *list = *tail = node;
  }
  else
  {
    (*tail)->next = node;
    *tail = node;
  }
}

static struct instruction *merge(struct instruction *l, struct instruction *r)
{
  struct instruction *ret = NULL, *tail = NULL, *tmp;

  while(l != NULL && r != NULL)
  {
    if(l->addr < r->addr)
    {
      tmp = l;
      l = l->next;
      append(&ret, &tail, tmp);
    }
    else
    {
      tmp = r;
      r = r->next;
      append(&ret, &tail, tmp);
    }
  }

  if(l == NULL) tail->next = r;
  else          tail->next = l;

  return ret;
}

static struct instruction *merge_sort(struct instruction *list, size_t n)
{
  struct instruction *left = NULL, *lt = NULL, *right = NULL, *rt = NULL;

  if(n <= 1) return list;

  for(size_t i = 0; i < n; i++)
  {
    struct instruction *tmp;

    tmp = list;
    list = list->next;

    if(i < n / 2) append(&left, &lt, tmp);
    else          append(&right, &rt, tmp);
  }

  left = merge_sort(left, n / 2);
  right = merge_sort(right, n - (n / 2));

  return merge(left, right);
}

static void sort_instructions(void)
{
  instructions = merge_sort(instructions, ninst);
}

static void free_instructions(void)
{
  struct instruction *tmp;

  while(instructions != NULL)
  {
    tmp = instructions;
    instructions = instructions->next;
    free(tmp->string);
    free(tmp);
  }
}

#define MAX_STORY_SIZE	524288

static unsigned long routines[MAX_STORY_SIZE];
static unsigned char seen_address[MAX_STORY_SIZE];

static struct opcode opcodes[5][256];

static void OP(enum count count, const char *name, int min, int max, int number, int flags)
{
  int v = zversion > 6 ? 5 : zversion;

  if(count > 4 || number > 255) errx("internal error: opcode %d %d is out of range", (int)count, number);

  if(v >= min && v <= max) opcodes[count][number] = (struct opcode){ .count = count, .number = number, .name = name, .flags = flags };
}

#define ZEROOP(...)	OP(ZERO, __VA_ARGS__)
#define ONEOP(...)	OP(ONE, __VA_ARGS__)
#define TWOOP(...)	OP(TWO, __VA_ARGS__)
#define VAROP(...)	OP(VAR, __VA_ARGS__)
#define EXTOP(...)	OP(EXT, __VA_ARGS__)

static void setup_opcodes(void)
{
  ZEROOP("rtrue",          1, 6, 0x00, F_RETURN);
  ZEROOP("rfalse",         1, 6, 0x01, F_RETURN);
  ZEROOP("print",          1, 6, 0x02, F_STRING);
  ZEROOP("print_ret",      1, 6, 0x03, F_RETURN | F_STRING);
  ZEROOP("nop",            1, 6, 0x04, 0);
  ZEROOP("save",           1, 3, 0x05, F_BRANCH);
  ZEROOP("save",           4, 4, 0x05, F_STORE);
  ZEROOP("restore",        1, 3, 0x06, F_BRANCH);
  ZEROOP("restore",        4, 4, 0x06, F_STORE);
  ZEROOP("restart",        1, 6, 0x07, F_RETURN);
  ZEROOP("ret_popped",     1, 6, 0x08, F_RETURN);
  ZEROOP("pop",            1, 4, 0x09, 0);
  ZEROOP("catch",          5, 6, 0x09, F_STORE);
  ZEROOP("quit",           1, 6, 0x0a, F_RETURN);
  ZEROOP("new_line",       1, 6, 0x0b, 0);
  ZEROOP("show_status",    3, 3, 0x0c, 0);
  ZEROOP("nop",            4, 6, 0x0c, 0);
  ZEROOP("verify",         3, 6, 0x0d, F_BRANCH);
  ZEROOP("piracy",         5, 6, 0x0f, F_BRANCH);

  ONEOP("jz",              1, 6, 0x00, F_BRANCH);
  ONEOP("get_sibling",     1, 6, 0x01, F_STORE | F_BRANCH);
  ONEOP("get_child",       1, 6, 0x02, F_STORE | F_BRANCH);
  ONEOP("get_parent",      1, 6, 0x03, F_STORE);
  ONEOP("get_prop_len",    1, 6, 0x04, F_STORE);
  ONEOP("inc",             1, 6, 0x05, F_INDIRECT);
  ONEOP("dec",             1, 6, 0x06, F_INDIRECT);
  ONEOP("print_addr",      1, 6, 0x07, 0);
  ONEOP("call_1s",         4, 6, 0x08, F_STORE | F_CALL1);
  ONEOP("remove_obj",      1, 6, 0x09, 0);
  ONEOP("print_obj",       1, 6, 0x0a, 0);
  ONEOP("ret",             1, 6, 0x0b, F_RETURN);
  ONEOP("jump",            1, 6, 0x0c, F_RETURN | F_JUMP);
  ONEOP("print_paddr",     1, 6, 0x0d, F_PSTRING);
  ONEOP("load",            1, 6, 0x0e, F_STORE | F_INDIRECT);
  ONEOP("not",             1, 4, 0x0f, F_STORE);
  ONEOP("call_1n",         5, 6, 0x0f, F_CALL1);

  TWOOP("je",              1, 6, 0x01, F_BRANCH);
  TWOOP("jl",              1, 6, 0x02, F_BRANCH);
  TWOOP("jg",              1, 6, 0x03, F_BRANCH);
  TWOOP("dec_chk",         1, 6, 0x04, F_BRANCH | F_INDIRECT);
  TWOOP("inc_chk",         1, 6, 0x05, F_BRANCH | F_INDIRECT);
  TWOOP("jin",             1, 6, 0x06, F_BRANCH);
  TWOOP("test",            1, 6, 0x07, F_BRANCH);
  TWOOP("or",              1, 6, 0x08, F_STORE);
  TWOOP("and",             1, 6, 0x09, F_STORE);
  TWOOP("test_attr",       1, 6, 0x0a, F_BRANCH);
  TWOOP("set_attr",        1, 6, 0x0b, 0);
  TWOOP("clear_attr",      1, 6, 0x0c, 0);
  TWOOP("store",           1, 6, 0x0d, F_INDIRECT);
  TWOOP("insert_obj",      1, 6, 0x0e, 0);
  TWOOP("loadw",           1, 6, 0x0f, F_STORE);
  TWOOP("loadb",           1, 6, 0x10, F_STORE);
  TWOOP("get_prop",        1, 6, 0x11, F_STORE);
  TWOOP("get_prop_addr",   1, 6, 0x12, F_STORE);
  TWOOP("get_next_prop",   1, 6, 0x13, F_STORE);
  TWOOP("add",             1, 6, 0x14, F_STORE);
  TWOOP("sub",             1, 6, 0x15, F_STORE);
  TWOOP("mul",             1, 6, 0x16, F_STORE);
  TWOOP("div",             1, 6, 0x17, F_STORE);
  TWOOP("mod",             1, 6, 0x18, F_STORE);
  TWOOP("call_2s",         4, 6, 0x19, F_STORE | F_CALL1);
  TWOOP("call_2n",         5, 6, 0x1a, F_CALL1);
  TWOOP("set_colour",      5, 6, 0x1b, 0);
  TWOOP("throw",           5, 6, 0x1c, 0);

  VAROP("call_vs",         1, 6, 0x00, F_STORE | F_CALL1);
  VAROP("storew",          1, 6, 0x01, 0);
  VAROP("storeb",          1, 6, 0x02, 0);
  VAROP("put_prop",        1, 6, 0x03, 0);
  VAROP("read",            1, 3, 0x04, 0);
  VAROP("read",            4, 4, 0x04, F_CALL3);
  VAROP("read",            5, 6, 0x04, F_STORE | F_CALL3);
  VAROP("print_char",      1, 6, 0x05, 0);
  VAROP("print_num",       1, 6, 0x06, 0);
  VAROP("random",          1, 6, 0x07, F_STORE);
  VAROP("push",            1, 6, 0x08, 0);
  VAROP("pull",            1, 5, 0x09, F_INDIRECT);
  VAROP("pull",            6, 6, 0x09, F_STORE);
  VAROP("split_window",    3, 6, 0x0a, 0);
  VAROP("set_window",      3, 6, 0x0b, 0);
  VAROP("call_vs2",        4, 6, 0x0c, F_STORE | F_CALL1);
  VAROP("erase_window",    4, 6, 0x0d, 0);
  VAROP("erase_line",      4, 6, 0x0e, 0);
  VAROP("set_cursor",      4, 6, 0x0f, 0);
  VAROP("get_cursor",      4, 6, 0x10, 0);
  VAROP("set_text_style",  4, 6, 0x11, 0);
  VAROP("buffer_mode",     4, 6, 0x12, 0);
  VAROP("output_stream",   3, 6, 0x13, 0);
  VAROP("input_stream",    3, 6, 0x14, 0);
  VAROP("sound_effect",    3, 4, 0x15, 0);
  VAROP("sound_effect",    5, 6, 0x15, F_CALL3);
  VAROP("read_char",       4, 6, 0x16, F_STORE | F_CALL2);
  VAROP("scan_table",      4, 6, 0x17, F_STORE | F_BRANCH);
  VAROP("not",             5, 6, 0x18, F_STORE);
  VAROP("call_vn",         5, 6, 0x19, F_CALL1);
  VAROP("call_vn2",        5, 6, 0x1a, F_CALL1);
  VAROP("tokenise",        5, 6, 0x1b, 0);
  VAROP("encode_text",     5, 6, 0x1c, 0);
  VAROP("copy_table",      5, 6, 0x1d, 0);
  VAROP("print_table",     5, 6, 0x1e, 0);
  VAROP("check_arg_count", 5, 6, 0x1f, F_BRANCH);

  EXTOP("save",            5, 6, 0x00, F_STORE);
  EXTOP("restore",         5, 6, 0x01, F_STORE);
  EXTOP("log_shift",       5, 6, 0x02, F_STORE);
  EXTOP("art_shift",       5, 6, 0x03, F_STORE);
  EXTOP("set_font",        5, 6, 0x04, F_STORE);
  EXTOP("draw_picture",    6, 6, 0x05, 0);
  EXTOP("picture_data",    6, 6, 0x06, F_BRANCH);
  EXTOP("erase_picture",   6, 6, 0x07, 0);
  EXTOP("set_margins",     6, 6, 0x08, 0);
  EXTOP("save_undo",       5, 6, 0x09, F_STORE);
  EXTOP("restore_undo",    5, 6, 0x0a, F_STORE);
  EXTOP("print_unicode",   5, 6, 0x0b, 0);
  EXTOP("check_unicode",   5, 6, 0x0c, F_STORE);
  EXTOP("set_true_colour", 5, 6, 0x0d, 0);
  EXTOP("move_window",     6, 6, 0x10, 0);
  EXTOP("window_size",     6, 6, 0x11, 0);
  EXTOP("window_style",    6, 6, 0x12, 0);
  EXTOP("get_wind_prop",   6, 6, 0x13, F_STORE);
  EXTOP("scroll_window",   6, 6, 0x14, 0);
  EXTOP("pop_stack",       6, 6, 0x15, 0);
  EXTOP("read_mouse",      6, 6, 0x16, 0);
  EXTOP("mouse_window",    6, 6, 0x17, 0);
  EXTOP("push_stack",      6, 6, 0x18, F_BRANCH);
  EXTOP("put_wind_prop",   6, 6, 0x19, 0);
  EXTOP("print_form",      6, 6, 0x1a, 0);
  EXTOP("make_menu",       6, 6, 0x1b, F_BRANCH);
  EXTOP("picture_table",   6, 6, 0x1c, 0);
  EXTOP("buffer_screen",   6, 6, 0x1d, 0);

  /* Zoom extensions. */
  EXTOP("start_timer",     5, 6, 0x80, 0);
  EXTOP("stop_timer",      5, 6, 0x81, 0);
  EXTOP("read_timer",      5, 6, 0x82, F_STORE);
  EXTOP("print_timer",     5, 6, 0x83, 0);
}

#undef ZEROOP
#undef ONEOP
#undef TWOOP
#undef VAROP
#undef EXTOP
#undef OP

static unsigned long unpack(uint32_t addr, int string)
{
  switch(zversion)
  {
    case 1: case 2: case 3:
      return addr * 2UL;
    case 4: case 5:
      return addr * 4UL;
    case 6: case 7:
      return (addr * 4UL) + (string ? S_O : R_O);
    case 8:
      return addr * 8UL;
  }

  errx("bad version %d", zversion);
}

/* Both constants and variables are stored in a long.  They are
 * differentiated by making sure that variables are always negative,
 * while the unsigned representations of constants are used, meaning
 * they will be positive (or zero).  Variables are encoded as the
 * negative value of the variable, minus one, so the stack pointer,
 * which is variable number 0, is stored as -1, the first local
 * (variable 1) is stored as -2, and so on.
 */
static long variable(int var)
{
  return -var - 1;
}

static void decode_var(uint8_t types, uint32_t *pc)
{
  for(int i = 6; i >= 0; i -= 2)
  {
    int type = (types >> i) & 0x03;

    if     (type == 0) args[nargs++] = WORD((*pc)++);
    else if(type == 1) args[nargs++] = BYTE(*pc);
    else if(type == 2) args[nargs++] = variable(BYTE(*pc));
    else return;

    (*pc)++;
  }
}

/* Given the (packed) address of a routine, this function returns the
 * address of the first instruction in the routine.  In addition, it
 * stores the address of the routine in a table so it can be identified
 * during the printout of the disassembly.
 */
static uint32_t handle_routine(uint32_t addr)
{
  uint8_t nlocals;
  uint32_t new;

  if(addr == 0) return 0;

  addr = unpack(addr, 0);
  new = addr;
  nlocals = BYTE(new++);
  if(zversion <= 4) new += (nlocals * 2);

  routines[new] = addr;

  return new;
}

static size_t znchars, zindex;
static char *zchars;

static void add_zchar(uint8_t c)
{
  if(zindex == znchars)
  {
    zchars = realloc(zchars, znchars += 256);
    if(zchars == NULL) err("realloc");
  }

  if(c == 13) c = newlinechar;

  zchars[zindex++] = c;
}

static int print_zcode(uint32_t addr, int in_abbr, void (*outc)(uint8_t))
{
  int abbrev = 0, shift = 0, special = 0;
  int c, lastc = 0; /* Initialize lastc to shut gcc up */
  uint16_t w;
  uint32_t counter = addr;
  int current_alphabet = 0;

  do
  {
    w = WORD(counter);

    for(int i = 10; i >= 0; i -= 5)
    {
      c = (w >> i) & 0x1f;

      if(special)
      {
        if(special == 2) lastc = c;
        else             outc((lastc << 5) | c);

        special--;
      }

      else if(abbrev)
      {
        uint32_t new_addr;

        new_addr = WORD(abbr_table + 64 * (abbrev - 1) + 2 * c);

        /* new_addr is a word address, so multiply by 2 */
        print_zcode(new_addr * 2, 1, outc);

        abbrev = 0;
      }

      else switch(c)
      {
        case 0:
          outc(' ');
          shift = 0;
          break;
        case 1:
          if(zversion == 1)
          {
            outc('\n');
            shift = 0;
            break;
          }
          /* fallthrough */
        case 2: case 3:
          if(zversion > 2 || (zversion == 2 && c == 1))
          {
            if(in_abbr) errx("abbreviation being used recursively");
            abbrev = c;
            shift = 0;
          }
          else
          {
            shift = c - 1;
          }
          break;
        case 4:
          if(zversion <= 2)
          {
            current_alphabet = (current_alphabet + 1) % 3;
            shift = 0;
          }
          else
          {
            shift = 1;
          }
          break;
        case 5:
          if(zversion <= 2)
          {
            current_alphabet = (current_alphabet + 2) % 3;
            shift = 0;
          }
          else
          {
            shift = 2;
          }
          break;
        case 6:
          if(zversion <= 2) shift = (current_alphabet + shift) % 3;
          if(shift == 2)
          {
            shift = 0;
            special = 2;
            break;
          }
          /* fallthrough */
        default:
          if(zversion <= 2 && c != 6) shift = (current_alphabet + shift) % 3;
          outc(atable[(26 * shift) + (c - 6)]);
          shift = 0;
          break;
      }
    }

    counter += 2;
  } while((w & 0x8000) == 0);

  return counter - addr;
}

/* Turn an argument into a string representation.  Values zero and above
 * are constants, whereas those below zero are variables.
 */
static const char *decode(long var, int store)
{
  static char ret[12];

  if(var < -256 || var > 65535) errx("invalid variable %ld", var);

  if(var >= 0)
  {
    snprintf(ret, sizeof ret, "#%02lx", (unsigned long)var);
  }
  else
  {
    var = -(var + 1);
    if(var == 0) strcpy(ret, store ? "-(SP)" : "(SP)+");
    else if(var <= 0x0f) snprintf(ret, sizeof ret, "L%02ld", var - 1);
    else snprintf(ret, sizeof ret, "G%02lx", (unsigned long)(var - 0x10));
  }

  return ret;
}

/* Begin interpreting at address “pc”.  If a call or branch instruction
 * is encountered, recursively call this function with the new address.
 * Because there is no “end of code” marker, interpretation has to stop
 * whenever we cannot be sure there is more code, which means opcodes
 * such as @rtrue, @quit, and @jump will terminate the current
 * interpretation loop, either returning to the previous loop or, if
 * this is the first call, returning to the initial caller.  Opcodes
 * that trigger this behavior have F_RETURN set.
 */
static void interpret(uint32_t pc, int indent, int verbose)
{
#define iprintf(...)	do { if(verbose) printf(__VA_ARGS__); } while(0)
  if(pc >= memory_size && verbose)
  {
    iprintf("%*s%04lx: outside of memory\n", indent * 2, "", (unsigned long)pc);
    if(ignore_errors) return;
    errx("cannot continiue");
  }

  while(1)
  {
    uint8_t opcode;
    unsigned long orig_pc;
    struct instruction inst = { 0 };
    int count, number;

    uint32_t newpc = 0;

    if(seen_address[pc]) return;

    seen_address[pc] = 1;

    orig_pc = pc;

    opcode = BYTE(pc++);

    /* long 2OP */
    if(opcode < 0x80)
    {
      nargs = 2;
      if(opcode & 0x40) args[0] = variable(BYTE(pc++));
      else              args[0] = BYTE(pc++);

      if(opcode & 0x20) args[1] = variable(BYTE(pc++));
      else              args[1] = BYTE(pc++);

      count = TWO;
      number = opcode & 0x1f;
    }

    /* short 1OP */
    else if(opcode < 0xb0)
    {
      nargs = 1;
      if(opcode < 0x90)
      {
        args[0] = WORD(pc);
        pc += 2;
      }
      else if(opcode < 0xa0)
      {
        args[0] = BYTE(pc++);
      }
      else
      {
        args[0] = variable(BYTE(pc++));
      }

      count = ONE;
      number = opcode & 0x0f;
    }

    /* 0OP */
    else if(opcode < 0xc0)
    {
      nargs = 0;

      count = ZERO;
      number = opcode & 0x0f;
    }

    /* variable 2OP */
    else if(opcode < 0xe0)
    {
      nargs = 0;

      decode_var(BYTE(pc++), &pc);

      count = TWO;
      number = opcode & 0x1f;
    }

    /* Double variable VAR */
    else if(opcode == 0xec || opcode == 0xfa)
    {
      uint8_t types1, types2;

      nargs = 0;

      types1 = BYTE(pc++);
      types2 = BYTE(pc++);
      decode_var(types1, &pc);
      decode_var(types2, &pc);

      count = VAR;
      number = opcode & 0x1f;
    }

    /* variable VAR */
    else
    {
      nargs = 0;

      decode_var(BYTE(pc++), &pc);

      count = VAR;
      number = opcode & 0x1f;
    }

    /* extended */
    if(count == ZERO && number == 0x0e)
    {
      nargs = 0;

      count = EXT;
      number = BYTE(pc++);

      decode_var(BYTE(pc++), &pc);
    }

    iprintf("%*s%04lx: ", indent * 2, "", orig_pc);

    inst.opcode = &opcodes[count][number];
    if(inst.opcode->name == NULL)
    {
      iprintf("unknown opcode %d %d\n", count, number);

      if(ignore_errors) return;

      if(verbose) errx("cannot continiue");
      else        errx("unknown opcode %d %d @%lx", count, number, orig_pc);
    }

    iprintf("%s ", inst.opcode->name);

    for(int i = 0; i < nargs; i++) iprintf("%s ", decode(args[i], 0));

    if(inst.opcode->flags & F_STORE)
    {
      inst.storeto = variable(BYTE(pc++));
      iprintf("-> %s", decode(inst.storeto, 1));
    }

    if(inst.opcode->flags & F_BRANCH)
    {
      uint8_t branch;
      uint16_t offset;

      branch = BYTE(pc++);

      offset = branch & 0x3f;

      if((branch & 0x40) == 0)
      {
        offset = (offset << 8) | BYTE(pc++);

        /* Get the sign right. */
        if(offset & 0x2000) offset |= 0xc000;
      }

      inst.invbranch = !(branch & 0x80);

      /* Branch to new offset from pc. */
      if(offset > 1)
      {
        newpc = pc + (int16_t)offset - 2;
        inst.branchto = newpc;
      }
      else
      {
        inst.branchto = offset;
      }

      if(inst.branchto > 1) iprintf("[%s] %lx", inst.invbranch ? "FALSE" : "TRUE", inst.branchto);
      else                  iprintf("[%s] %s",  inst.invbranch ? "FALSE" : "TRUE", inst.branchto == 1 ? "RTRUE" : "RFALSE");
    }

    zindex = 0;

    if(inst.opcode->flags & F_STRING)
    {
      pc += print_zcode(pc, 0, add_zchar);
    }

    if((inst.opcode->flags & F_PSTRING) && args[0] > 0)
    {
      print_zcode(unpack(args[0], 1), 0, add_zchar);
      nargs = 0;
    }

    if(zindex != 0)
    {
      inst.string = malloc(zindex + 1);
      if(inst.string == NULL) err("malloc");
      memcpy(inst.string, zchars, zindex);
      inst.string[zindex] = 0;
    }

    if(inst.opcode->flags & F_CALL1)
    {
      if(args[0] > 0) newpc = handle_routine(args[0]);
    }

    if(inst.opcode->flags & F_CALL2)
    {
      if(nargs == 3 && args[2] > 0) newpc = handle_routine(args[2]);
    }

    if(inst.opcode->flags & F_CALL3)
    {
      if(nargs == 4 && args[3] > 0) newpc = handle_routine(args[3]);
    }

    if((inst.opcode->flags & F_JUMP) && args[0] >= 0)
    {
      newpc = pc + (int16_t)args[0] - 2;
    }

    if(inst.opcode->flags & F_INDIRECT)
    {
      args[0] = variable(args[0]);
    }

    inst.addr = orig_pc;
    inst.nextaddr = pc;

    inst.nargs = nargs;
    for(int i = 0; i < nargs; i++) inst.args[i] = args[i];

    add_instruction(inst);

    iprintf("\n");

    if(newpc != 0) interpret(newpc, indent + 1, verbose);

    if(inst.opcode->flags & F_RETURN) return;
  }
}

static unsigned long roundup(unsigned long v, unsigned long multiple)
{
  return ((v + multiple - 1) / multiple) * multiple;
}

static void print_code(void)
{
  uint32_t lastaddr = 0;

  sort_instructions();

  for(struct instruction *inst = instructions; inst != NULL; inst = inst->next)
  {
    /* If the last instruction does not directly abut the current
     * instruction, there is a gap (probably caused by a jump of some
     * sort); represent that with a newline...
     */
    if(lastaddr != inst->addr) putchar('\n');

    /* ... except that it’s possible for the start of the main routine
     * (which really isn’t a routine since it has no header) to be
     * adjacent to a routine placed right before it.  In this case,
     * there should be a newline, so add it.
     */
    if(inst->addr == main_routine) printf("%sMAIN ROUTINE %lx\n", lastaddr == inst->addr ? "\n" : "", inst->addr - 1);
    else if(routines[inst->addr]) printf("ROUTINE %lx\n", routines[inst->addr]);

    lastaddr = inst->nextaddr;

    printf("%6lx: ", inst->addr);

    if(dumphex)
    {
      /* Strings can be very long, so don’t dump unless requested. */
      if(!dumpstring && inst->opcode->flags & F_STRING)
      {
        printf("%02x ...%*s", (unsigned)memory[inst->addr], (print_width * 3) - 6, "");
      }
      else
      {
        for(unsigned long i = 0; i < roundup(inst->nextaddr - inst->addr, print_width); i++)
        {
          if(i > 0 && i % print_width == 0) printf("\n%8s", "");

          if(inst->addr + i < inst->nextaddr) printf("%02x ", (unsigned)memory[inst->addr + i]);
          else                                printf("   ");
        }
      }

      putchar(' ');
    }

    printf("%-16s ", inst->opcode->name);

    if(inst->string != NULL) printf("%s ", inst->string);

    if((inst->opcode->flags & F_CALL1) && inst->args[0] >= 0)
    {
      printf("#%lx ", unpack(inst->args[0], 0));
      for(int i = 1; i < inst->nargs; i++) printf("%s ", decode(inst->args[i], 0));
    }
    else if((inst->opcode->flags & F_JUMP) && inst->args[0] >= 0)
    {
      printf("#%lx ", inst->addr + (int16_t)inst->args[0] + 1);
    }
    else
    {
      for(int i = 0; i < inst->nargs; i++) printf("%s ", decode(inst->args[i], 0));
    }

    if(inst->opcode->flags & F_STORE) printf("-> %s ", decode(inst->storeto, 1));

    if(inst->opcode->flags & F_BRANCH)
    {
      if(inst->branchto > 1) printf("[%s] %lx", inst->invbranch ? "FALSE" : "TRUE", inst->branchto);
      else                   printf("[%s] %s",  inst->invbranch ? "FALSE" : "TRUE", inst->branchto == 1 ? "RTRUE" : "RFALSE");
    }

    putchar('\n');
  }
}

int main(int argc, char **argv)
{
  int c;
  int vflag = 0;
  FILE *fp;
  uint32_t start;
  static const size_t MAXADDR = 1024;
  size_t naddr = 0;
  uint32_t addr[MAXADDR];
  struct stat st;

  while((c = getopt(argc, argv, "a:A:bdDinvw:")) != -1)
  {
    switch(c)
    {
      case 'a':
        if(naddr == MAXADDR) errx("too many addresses: max %zu", MAXADDR);
        addr[naddr++] = strtoul(optarg, NULL, 16);
        break;
      case 'A':
        {
          char line[16];

          if(strcmp(optarg, "-") == 0)
          {
            fp = stdin;
          }
          else
          {
            fp = fopen(optarg, "r");
            if(fp == NULL) err("%s", optarg);
          }

          while(fgets(line, sizeof line, fp) != NULL)
          {
            if(naddr == MAXADDR) errx("too many addresses: max %zu", MAXADDR);
            addr[naddr++] = strtoul(line, NULL, 16);
          }

          if(fp != stdin) fclose(fp);
        }
        break;
      case 'b':
        setvbuf(stdout, NULL, _IONBF, 0);
        break;
      case 'd':
        dumphex = 1;
        break;
      case 'D':
        dumpstring = 1;
        break;
      case 'i':
        ignore_errors = 1;
        break;
      case 'n':
        newlinechar = '^';
        break;
      case 'v':
        vflag = 1;
        break;
      case 'w':
        print_width = strtol(optarg, NULL, 10);
        if(print_width <= 0) print_width = 8;
        break;
      default:
        exit(1);
    }
  }

  if(argc - optind != 1) errx("bad call");

  fp = fopen(argv[optind], "rb");
  if(fp == NULL) err("%s", argv[optind]);

  if(fstat(fileno(fp), &st) == -1) err("fstat");

  if(st.st_size > MAX_STORY_SIZE) errx("file too large");

  memory = malloc(memory_size = st.st_size);
  if(memory == NULL) err("malloc");

  if(fread(memory, memory_size, 1, fp) != 1) errx("short read");

  fclose(fp);

  zversion   = BYTE(0);
  start      = WORD(0x06);
  abbr_table = WORD(0x18);

  if(zversion == 0 || zversion > 8) errx("unknown z-machine version %d", zversion);

  if(zversion == 6 || zversion == 7)
  {
    R_O = WORD(0x28) * 8UL;
    S_O = WORD(0x2a) * 8UL;
  }

  if(zversion == 1)
  {
    memcpy(&atable[26 * 2], " 0123456789.,!?_#'\"/\\<-:()", 26);
  }
  else if(zversion >= 5 && WORD(0x34) != 0)
  {
    if(WORD(0x34) + 26 * 3 >= memory_size) errx("corrupted story: alphabet table out of range");

    memcpy(atable, &memory[WORD(0x34)], 26 * 3);
    atable[52] = 0x00;
    atable[53] = 0x0d;
  }

  if(zversion == 6) start = handle_routine(start);

  main_routine = start;

  setup_opcodes();

  if(naddr == 0)
  {
    addr[naddr++] = start;
  }
  else
  {
    for(size_t i = 0; i < naddr; i++)
    {
      if(addr[i] == 0)
      {
        addr[i] = start;
      }
      else
      {
        uint32_t orig = addr[i];

        if(zversion <= 4) addr[i] += (2 * BYTE(addr[i]));

        addr[i]++;
        routines[addr[i]] = orig;
      }
    }
  }

  for(size_t i = 0; i < naddr; i++)
  {
    if(vflag) printf("Beginning disassembly at %lx\n"
                     "-----------------------------\n",
                     (unsigned long)addr[i]);
    interpret(addr[i], 0, vflag);
    if(vflag) putchar('\n');
  }

  print_code();

  free(memory);
  free(zchars);

  free_instructions();

  return 0;
}
