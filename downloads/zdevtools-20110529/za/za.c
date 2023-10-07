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
#include <stdint.h>
#include <string.h>
#include <stdarg.h>
#include <errno.h>
#include <limits.h>
#include <time.h>

#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <regex.h>

#define ASIZE(a)	(sizeof (a) / sizeof *(a))

/* These are for system/usage errors (malloc() failure, invalid
 * command-line argument, etc.).
 */
#define err(...)	do { fprintf(stderr, __VA_ARGS__); fprintf(stderr, ": %s\n", strerror(errno)); exit(1); } while(0)
#define errx(...)	do { fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); exit(1); } while(0)

/* These are for syntax errors. */
static const char *current_file;
static char current_line[1024];
static int current_lineno;
static void msg(const char *type, const char *fmt, ...)
{
  va_list ap;

  va_start(ap, fmt);

  /* Messages can be generated before the file is parsed. */
  if(current_file == NULL)
  {
    fprintf(stderr, "internal %s: ", type);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
  }
  else
  {
    fprintf(stderr, "%s:%d: %s: ", current_file, current_lineno, type);
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n\t%s\n\t^\n", current_line);
  }

  va_end(ap);
}
#define die(...)	do { msg("error", __VA_ARGS__); exit(1); } while(0)
#define warning(...)	msg("warning", __VA_ARGS__)

static long release = 1;
static char serial[7];

static long zversion = 8;

/* Return routine alignment for a particular Z-machine version.  In
 * addition to being used when a routine is created, this also is used
 * as the divisor when storing the file size and as the default
 * alignment for the “align” directive.
 */
static int alignment(void)
{
  switch(zversion)
  {
    case 1: case 2: case 3:
      return 2;
    case 4: case 5: case 6: case 7:
      return 4;
    case 8:
      return 8;
    default:
      errx("unsupported version %ld", zversion);
  }
}

/* Pack an address; this does not currently understand routine/string
 * offsets of V6 and V7 (they are both set to zero), so routines at the
 * top of memory will not properly pack.
 */
static uint32_t pack(uint32_t a)
{
  return a / alignment();
}

static unsigned long max_size(void)
{
  switch(zversion)
  {
    case 1: case 2: case 3:
      return 131072UL;
    case 4: case 5:
      return 262144UL;
    case 7:
      return 327680UL;
    case 6: case 8:
      return 524288UL;
    default:
      errx("unsupported version %ld", zversion);
  }
}

static int fd;

static void WRITE(const void *b, ssize_t l) { if(write(fd, b, l) != l) errx("short write"); }
static void PWRITE(const void *b, ssize_t l, off_t o) { if(pwrite(fd, b, l, o) != l) errx("short write"); }
static void BYTE(uint8_t v) { WRITE(&v, 1); }
static void PBYTE(uint8_t v, off_t o) { PWRITE(&v, 1, o); }
static void WORD(uint16_t v) { BYTE(v >> 8); BYTE(v & 0xff); }
static void PWORD(uint16_t v, off_t o) { PBYTE(v >> 8, o); PBYTE(v & 0xff, o + 1); }
static void SEEK(off_t o, int w) { if(lseek(fd, o, w) == -1) err("lseek"); }
static off_t TELL(void) { off_t r = lseek(fd, 0, SEEK_CUR); if(r == -1) err("lseek"); return r; }

static unsigned long roundup(unsigned long v, unsigned long multiple)
{
  if(multiple == 0) return 0;

  return multiple * (((v - 1) / multiple) + 1);
}

static uint32_t ALIGN(uint32_t v) { return roundup(v, alignment()); }
static void SEEKALIGN(void) { SEEK(ALIGN(TELL()), SEEK_SET); }

#define UNICODE_TABLE_SIZE	97
static uint16_t unicode_table[UNICODE_TABLE_SIZE];
static int unicode_index;
static uint8_t unicode_to_zscii(uint16_t u)
{
  if(unicode_index > 0)
  {
    for(int i = 0; i < unicode_index; i++)
    {
      if(unicode_table[i] == u) return i + 155;
    }
  }

  if(unicode_index == UNICODE_TABLE_SIZE) die("too many unicode characters for the table (max %d)", UNICODE_TABLE_SIZE);
  unicode_table[unicode_index++] = u;

  return unicode_index + 154;
}

static size_t decode_utf8(const char *string, uint16_t *utf)
{
  uint16_t *saved = utf;
  uint32_t ret;

  for(const char *p = string; *p != 0; p++)
  {
    if((*p & 0x80) == 0) /* One byte. */
    {
      ret = *p;
    }
    else if((*p & 0xe0) == 0xc0) /* Two bytes. */
    {
      if(p[1] == 0) die("invalid utf-8 sequence at byte %d", (int)(p - string));

      ret  = (*p++ & 0x1f) << 6;
      ret |= (*p   & 0x3f);
    }
    else if((*p & 0xf0) == 0xe0) /* Three bytes. */
    {
      if(p[1] == 0 || p[2] == 0) die("invalid utf-8 sequence at byte %d", (int)(p - string));

      ret  = (*p++ & 0x0f) << 12;
      ret |= (*p++ & 0x3f) << 6;
      ret |= (*p   & 0x3f);
    }
    else if((*p & 0xf8) == 0xf0)
    {
      die("4-byte utf-8 is not supported, byte %d", (int)(p - string));
    }
    else
    {
      die("invalid utf-8 sequence at byte %d", (int)(p - string));
    }

    if(ret > UINT16_MAX) die("too-large unicode value");

    *utf++ = ret;
  }

  return utf - saved;
}

#define F_INDIRECT	0x01
#define F_JUMP		0x02
#define F_2VAR		0x04
#define F_DOUBLE	0x08

struct opcode
{
  enum count { C_ZERO, C_ONE, C_TWO, C_VAR, C_EXT } count;
  int number;

  const char *name;
  const char *prototype;
  regex_t re;
  int flags;
};

static struct opcode opcodes[256];
static size_t nopcodes = 0;

static void OP_(enum count count, const char *name, int min, int max, int number, const char *prototype, int flags)
{
  int v = zversion > 6 ? 5 : zversion;
  int e;

  if(v < min || v > max) return;

  /* An extra slot at the end of the opcodes list is reserved as a
   * sentinel: the “name” member will be NULL.
   */
  if(nopcodes >= (sizeof opcodes / sizeof *opcodes) - 1) errx("internal error: opcode overflow");

  opcodes[nopcodes] = (struct opcode){ .count = count, .name = name, .number = number, .prototype = prototype, .flags = flags };

  e = regcomp(&opcodes[nopcodes].re, opcodes[nopcodes].prototype, REG_EXTENDED | REG_NOSUB);
  if(e != 0)
  {
    char emsg[256];
    regerror(e, &opcodes[nopcodes].re, emsg, sizeof emsg);
    errx("error compiling %s: %s", opcodes[nopcodes].prototype, emsg);
  }

  nopcodes++;
}

#define OP(count, name, min, max, number, prototype, flags)	OP_(count, name, min, max, number, "^" prototype "$", flags)

#define ZEROOP(...)	OP(C_ZERO, __VA_ARGS__)
#define ONEOP(...)	OP(C_ONE, __VA_ARGS__)
#define TWOOP(...)	OP(C_TWO, __VA_ARGS__)
#define VAROP(...)	OP(C_VAR, __VA_ARGS__)
#define EXTOP(...)	OP(C_EXT, __VA_ARGS__)

/* Convenience macros.  The arguments to most opcodes can be of any
 * type, so provide easy ways to accomplish this.
 */
#define NONE	""
#define ONE	"[vn]"
#define TWO	"[vn][vn]"
#define THREE	"[vn][vn][vn]"
#define FOUR	"[vn][vn][vn][vn]"
#define BRANCH	"\\?"
#define STORE	">v"

static void setup_opcodes(void)
{
  ZEROOP("rtrue",          1, 6, 0x00, NONE, 0);
  ZEROOP("rfalse",         1, 6, 0x01, NONE, 0);
  ZEROOP("nop",            1, 6, 0x04, NONE, 0);
  ZEROOP("save",           1, 3, 0x05, BRANCH, 0);
  ZEROOP("save",           4, 4, 0x05, STORE, 0);
  ZEROOP("restore",        1, 3, 0x06, BRANCH, 0);
  ZEROOP("restore",        4, 4, 0x06, STORE, 0);
  ZEROOP("restart",        1, 6, 0x07, NONE, 0);
  ZEROOP("ret_popped",     1, 6, 0x08, NONE, 0);
  ZEROOP("pop",            1, 4, 0x09, NONE, 0);
  ZEROOP("catch",          5, 6, 0x09, NONE STORE, 0);
  ZEROOP("quit",           1, 6, 0x0a, NONE, 0);
  ZEROOP("new_line",       1, 6, 0x0b, NONE, 0);
  ZEROOP("show_status",    3, 3, 0x0c, NONE, 0);
  ZEROOP("verify",         3, 6, 0x0d, NONE BRANCH, 0);
  ZEROOP("piracy",         5, 6, 0x0f, NONE BRANCH, 0);

  ONEOP("jz",              1, 6, 0x00, ONE BRANCH, 0);
  ONEOP("get_sibling",     1, 6, 0x01, ONE BRANCH STORE, 0);
  ONEOP("get_child",       1, 6, 0x02, ONE BRANCH STORE, 0);
  ONEOP("get_parent",      1, 6, 0x03, ONE STORE, 0);
  ONEOP("get_prop_len",    1, 6, 0x04, ONE STORE, 0);
  ONEOP("inc",             1, 6, 0x05, "v", F_INDIRECT);
  ONEOP("dec",             1, 6, 0x06, "v", F_INDIRECT);
  ONEOP("print_addr",      1, 6, 0x07, ONE, 0);
  ONEOP("call_1s",         4, 6, 0x08, ONE STORE, 0);
  ONEOP("remove_obj",      1, 6, 0x09, ONE, 0);
  ONEOP("print_obj",       1, 6, 0x0a, ONE, 0);
  ONEOP("ret",             1, 6, 0x0b, ONE, 0);
  ONEOP("jump",            1, 6, 0x0c, BRANCH, F_JUMP);
  ONEOP("print_paddr",     1, 6, 0x0d, ONE, 0);
  ONEOP("load",            1, 6, 0x0e, "v" STORE, F_INDIRECT);
  ONEOP("not",             1, 4, 0x0f, ONE STORE, 0);
  ONEOP("call_1n",         5, 6, 0x0f, ONE, 0);

  TWOOP("je",              1, 6, 0x01, "[vn][vn]{0,3}" BRANCH, F_2VAR);
  TWOOP("jl",              1, 6, 0x02, TWO BRANCH, 0);
  TWOOP("jg",              1, 6, 0x03, TWO BRANCH, 0);
  TWOOP("dec_chk",         1, 6, 0x04, "v[vn]" BRANCH, F_INDIRECT);
  TWOOP("inc_chk",         1, 6, 0x05, "v[vn]" BRANCH, F_INDIRECT);
  TWOOP("jin",             1, 6, 0x06, TWO BRANCH, 0);
  TWOOP("test",            1, 6, 0x07, TWO BRANCH, 0);
  TWOOP("or",              1, 6, 0x08, TWO STORE, 0);
  TWOOP("and",             1, 6, 0x09, TWO STORE, 0);
  TWOOP("test_attr",       1, 6, 0x0a, TWO BRANCH, 0);
  TWOOP("set_attr",        1, 6, 0x0b, TWO, 0);
  TWOOP("clear_attr",      1, 6, 0x0c, TWO, 0);
  TWOOP("store",           1, 6, 0x0d, "v[vn]", F_INDIRECT);
  TWOOP("insert_obj",      1, 6, 0x0e, TWO, 0);
  TWOOP("loadw",           1, 6, 0x0f, TWO STORE, 0);
  TWOOP("loadb",           1, 6, 0x10, TWO STORE, 0);
  TWOOP("get_prop",        1, 6, 0x11, TWO STORE, 0);
  TWOOP("get_prop_addr",   1, 6, 0x12, TWO STORE, 0);
  TWOOP("get_next_prop",   1, 6, 0x13, TWO STORE, 0);
  TWOOP("add",             1, 6, 0x14, TWO STORE, 0);
  TWOOP("sub",             1, 6, 0x15, TWO STORE, 0);
  TWOOP("mul",             1, 6, 0x16, TWO STORE, 0);
  TWOOP("div",             1, 6, 0x17, TWO STORE, 0);
  TWOOP("mod",             1, 6, 0x18, TWO STORE, 0);
  TWOOP("call_2s",         4, 6, 0x19, TWO STORE, 0);
  TWOOP("call_2n",         5, 6, 0x1a, TWO, 0);
  TWOOP("set_colour",      5, 5, 0x1b, TWO, 0);
  TWOOP("set_colour",      6, 6, 0x1b, "[vn][vn][vn]?", F_2VAR);
  TWOOP("throw",           5, 6, 0x1c, TWO, 0);

  VAROP("call_vs",         1, 6, 0x00, "[vn][vn]{0,3}" STORE, 0);
  VAROP("storew",          1, 6, 0x01, THREE, 0);
  VAROP("storeb",          1, 6, 0x02, THREE, 0);
  VAROP("put_prop",        1, 6, 0x03, THREE, 0);
  VAROP("read",            1, 3, 0x04, TWO, 0);
  VAROP("read",            4, 4, 0x04, "[vn][vn]([vn][vn])?", 0);
  VAROP("read",            5, 6, 0x04, "[vn][vn]([vn][vn])?" STORE, 0);
  VAROP("print_char",      1, 6, 0x05, ONE, 0);
  VAROP("print_num",       1, 6, 0x06, ONE, 0);
  VAROP("random",          1, 6, 0x07, ONE STORE, 0);
  VAROP("push",            1, 6, 0x08, ONE, 0);
  VAROP("pull",            1, 5, 0x09, "v", F_INDIRECT);
  VAROP("pull",            6, 6, 0x09, "[vn]?" STORE, 0);
  VAROP("split_window",    3, 6, 0x0a, ONE, 0);
  VAROP("set_window",      3, 6, 0x0b, ONE, 0);
  VAROP("call_vs2",        4, 6, 0x0c, "[vn][vn]{0,7}" STORE, F_DOUBLE);
  VAROP("erase_window",    4, 6, 0x0d, ONE, 0);
  VAROP("erase_line",      4, 6, 0x0e, ONE, 0);
  VAROP("set_cursor",      4, 5, 0x0f, TWO, 0);
  VAROP("set_cursor",      6, 6, 0x0f, THREE, 0);
  VAROP("get_cursor",      4, 6, 0x10, ONE, 0);
  VAROP("set_text_style",  4, 6, 0x11, ONE, 0);
  VAROP("buffer_mode",     4, 6, 0x12, ONE, 0);
  VAROP("output_stream",   3, 4, 0x13, ONE, 0);
  VAROP("output_stream",   5, 5, 0x13, "[vn][vn]?", 0);
  VAROP("output_stream",   6, 6, 0x13, "[vn][vn]{0,2}", 0);
  VAROP("input_stream",    3, 6, 0x14, ONE, 0);
  VAROP("sound_effect",    3, 6, 0x15, FOUR, 0);
  VAROP("read_char",       4, 6, 0x16, "[vn]([vn][vn])?" STORE, 0);
  VAROP("scan_table",      4, 6, 0x17, "[vn][vn][vn][vn]?" BRANCH STORE, 0);
  VAROP("not",             5, 6, 0x18, ONE STORE, 0);
  VAROP("call_vn",         5, 6, 0x19, "[vn][vn]{0,3}", 0);
  VAROP("call_vn2",        5, 6, 0x1a, "[vn][vn]{0,7}", F_DOUBLE);
  VAROP("tokenise",        5, 6, 0x1b, FOUR, 0);
  VAROP("encode_text",     5, 6, 0x1c, FOUR, 0);
  VAROP("copy_table",      5, 6, 0x1d, THREE, 0);
  VAROP("print_table",     5, 6, 0x1e, "[vn][vn][vn]{0,2}", 0);
  VAROP("check_arg_count", 5, 6, 0x1f, ONE BRANCH, 0);

  EXTOP("save",            5, 6, 0x00, "([vn]{3})?" STORE, 0);
  EXTOP("restore",         5, 6, 0x01, "([vn]{3})?" STORE, 0);
  EXTOP("log_shift",       5, 6, 0x02, TWO STORE, 0);
  EXTOP("art_shift",       5, 6, 0x03, TWO STORE, 0);
  EXTOP("set_font",        5, 6, 0x04, ONE STORE, 0);
  EXTOP("draw_picture",    6, 6, 0x05, "[vn][vn]{0,2}", 0);
  EXTOP("picture_data",    6, 6, 0x06, TWO BRANCH, 0);
  EXTOP("erase_picture",   6, 6, 0x07, THREE, 0);
  EXTOP("set_margins",     6, 6, 0x08, THREE, 0);
  EXTOP("save_undo",       5, 6, 0x09, STORE, 0);
  EXTOP("restore_undo",    5, 6, 0x0a, STORE, 0);
  EXTOP("print_unicode",   5, 6, 0x0b, ONE, 0);
  EXTOP("check_unicode",   5, 6, 0x0c, ONE STORE, 0);
  EXTOP("set_true_colour", 5, 5, 0x0d, TWO, 0);
  EXTOP("set_true_colour", 6, 6, 0x0d, THREE, 0);
  EXTOP("move_window",     6, 6, 0x10, THREE, 0);
  EXTOP("window_size",     6, 6, 0x11, THREE, 0);
  EXTOP("window_style",    6, 6, 0x12, "[vn][vn][vn]?", 0);
  EXTOP("get_wind_prop",   6, 6, 0x13, TWO STORE, 0);
  EXTOP("scroll_window",   6, 6, 0x14, TWO, 0);
  EXTOP("pop_stack",       6, 6, 0x15, "[vn][vn]?", 0);
  EXTOP("read_mouse",      6, 6, 0x16, ONE, 0);
  EXTOP("mouse_window",    6, 6, 0x17, "[vn]?", 0);
  EXTOP("push_stack",      6, 6, 0x18, TWO BRANCH, 0);
  EXTOP("put_wind_prop",   6, 6, 0x19, THREE, 0);
  EXTOP("print_form",      6, 6, 0x1a, ONE, 0);
  EXTOP("make_menu",       6, 6, 0x1b, TWO BRANCH, 0);
  EXTOP("picture_table",   6, 6, 0x1c, ONE, 0);

  /* Zoom extensions. */
  EXTOP("start_timer",     5, 6, 0x80, NONE, 0);
  EXTOP("stop_timer",      5, 6, 0x81, NONE, 0);
  EXTOP("read_timer",      5, 6, 0x82, STORE, 0);
  EXTOP("print_timer",     5, 6, 0x83, NONE, 0);
}

#undef NONE
#undef ONE
#undef TWO
#undef THREE
#undef FOUR
#undef BRANCH
#undef STORE

#undef ZEROOP
#undef ONEOP
#undef TWOOP
#undef VAROP
#undef EXTOP
#undef OP

static char *xstrdup(const char *s)
{
  char *r;
  size_t l;

  l = strlen(s);

  r = malloc(l + 1);
  if(r == NULL) err("malloc");

  memcpy(r, s, l + 1);

  return r;
}

/* Each operand to an opcode is represented by a “struct arg”.
 * There are four types:
 * • none, indicating no argument
 * • jump, indicating an argument that is a label
 * • numeric, indicating a constant (large or small)
 * • variable, indicating a variable.
 *
 * jump_type indicates whether the jump is a routine, label, or branch.
 *
 * value indicates the value for a numeric or variable (for a variable,
 * 0 is the stack pointer, 1 is local var 1, etc., as in the standard.)
 *
 * name is the name of the label to branch to.
 *
 * small is true if this is a one-byte (6-bit) offset as opposed to a
 * two-byte (14-bit) offset.
 *
 * invert is true if the argument is a branch target and the test should
 * be inverted (branch on false).
 *
 * ret is set to 0 or 1 if the branch, instead of branching, should
 * return false or true; this value should be checked iff name is NULL.
 */
struct arg
{
  enum { A_NONE, A_JUMP, A_NUMERIC, A_VARIABLE } type;
  enum jump_type { J_BRANCH, J_JUMP, J_LABEL, J_PACKED } jump_type;

  uint16_t value;
  char *name;

  int small;
  int invert;
  int ret;
};

/* Information on each label that’s found (either a label for jumping
 * to, or a routine name).
 * “name” is the name, and “addr” is the location of the label.  Note
 * that a single list is used so routines and labels cannot have the
 * same name.
 */
struct label
{
  const char *name;
  uint32_t addr;

  struct label *next;
};

static struct label *labels = NULL;

static void add_label(const char *name, uint32_t addr)
{
  struct label *new;

  for(new = labels; new != NULL; new = new->next)
  {
    if(strcmp(new->name, name) == 0) die("label %s already exists", name);
  }

  new = malloc(sizeof *new);
  if(new == NULL) err("malloc");

  new->name = xstrdup(name);
  new->addr = addr;

  new->next = labels;
  labels = new;
}

/* Each jump struct represents a jump: either a routine call, a jump, or
 * a branch instruction.
 * “from” is the address whence the jump occurs, and “to” is the label
 * to which a jump is requested.
 * If the type is a branch, “small” is set if this is a one-byte (6-bit)
 * offset, and “invert” is set if the branch should be taken in the
 * false case.
 */
struct jump
{
  enum jump_type type;
  uint32_t from;
  const char *to;

  int small;
  int invert;

  char *file;
  char *line;
  int lineno;

  struct jump *next;
};

static struct jump *jumps = NULL;

static void add_jump(struct arg jump)
{
  struct jump *new;

  if(jump.jump_type == J_BRANCH && jump.name == NULL)
  {
    BYTE((!jump.invert << 7) | 0x40 | jump.ret);
    return;
  }

  /* @jump ? is special-cased because the syntax is natural, but
   * allowing ? also allows ?0, ?~, and %, so catch those errors here.
   */
  if(jump.jump_type == J_JUMP)
  {
    if(jump.name == NULL || jump.invert || jump.small) die("syntax: jump ?Label");
  }

  new = malloc(sizeof *new);
  if(new == NULL) err("malloc");

  new->type = jump.jump_type;
  new->from = TELL();
  new->to = xstrdup(jump.name);
  if(jump.jump_type == J_BRANCH)
  {
    new->small = jump.small;
    new->invert = jump.invert;
  }

  new->file = xstrdup(current_file);
  new->line = xstrdup(current_line);
  new->lineno = current_lineno;

  new->next = jumps;
  jumps = new;

  if(jump.small) BYTE(0);
  else           WORD(0);
}

static void apply_jumps(void)
{
  for(struct jump *j = jumps; j != NULL; j = j->next)
  {
    int found = 0;

    current_file = j->file;
    strcpy(current_line, j->line); /* guaranteed to be large enough because j->line was originally copied from current_line. */
    current_lineno = j->lineno;

    for(struct label *l = labels; l != NULL; l = l->next)
    {
      if(strcmp(l->name, j->to) == 0)
      {
        found = 1;
        switch(j->type)
        {
          uint16_t offset;
          long long tempo;

          case J_BRANCH:
            tempo = (long long)l->addr - (long long)j->from;

            if(j->small)
            {
              /* The offset needs to have two added to it (decoding the
               * offset is done as PC = PC + Offset - 2); at this point
               * j->from is at the part right where the offset is
               * written.  It is therefore, if the offset is 16 bits,
               * already two bytes farther than is “correct”, or if the
               * offset is 8 bits, one byte farther; so in this case one
               * needs to be added on.
               *
               * 61 01 01 c2
               *          ^  ^
               *
               * 61 is @je, 01 01 is L01 L01.  The first arrow points to
               * where the offset is stored, which is also where j->from
               * is currently pointing.  The second arrow is the
               * location whence the offset should be counted.  Since
               * the offset is calculated by using j->from as the
               * starting address, it is already one byte longer than is
               * the “actual” offset, which means it it one byte shorter
               * than the *stored* offset needs to be.  Adding one gives
               * the proper value.
               */
              tempo++;

              if(tempo < 0 || tempo > 63) die("offset (%lld) does not fit into unsigned 6-bit value", tempo);

              offset = tempo;
              offset &= 0x3f;

              offset |= 0x40;
              if(!j->invert) offset |= 0x80;

              PBYTE(offset, j->from);
            }
            else
            {
              /* A quick example of the offset wackiness as described
               * above, for a 14-bit offset.
               *
               * 61 01 01 80 02
               *          ^     ^
               *
               * Here again the first arrow is where j->from is
               * pointing, whereas the second arrow is whence the offset
               * is counted.  This time, the two bytes needed for the
               * stored value are already present if j->from is used as
               * the starting point, so nothing special needs to be
               * done.
               */
              if(tempo < -8192 || tempo > 8191) die("offset (%lld) does not fit into signed 14-bit value", tempo);

              offset = tempo;
              offset &= 0x3fff;
              if(!j->invert) offset |= 0x8000;

              PWORD(offset, j->from);
            }

            break;
          case J_JUMP:
            tempo = (long long)l->addr - (long long)j->from;
            if(tempo < INT16_MIN || tempo > INT16_MAX) die("offset (%lld) does not fit into signed 16-bit value", tempo);

            PWORD(tempo, j->from);

            break;
          case J_LABEL:
            if(l->addr > UINT16_MAX) die("address of %s is too large (%lx)", l->name, (unsigned long)l->addr);
            PWORD(l->addr, j->from);

            break;
          case J_PACKED:
            if(pack(l->addr) > UINT16_MAX) die("address of %s is too large to pack (%lx -> %lx)", l->name, (unsigned long)l->addr, (unsigned long)pack(l->addr));
            PWORD(pack(l->addr), j->from);

            break;
        }

        break;
      }
    }

    if(!found) die("no label %s", j->to);
  }
}

static struct arg NONE(void)			{ return (struct arg){ .type = A_NONE }; }
static struct arg N(uint16_t n)			{ return (struct arg){ .type = A_NUMERIC, .value = n }; }
static struct arg SP(void)			{ return (struct arg){ .type = A_VARIABLE, .value = 0 }; }
static struct arg L(uint8_t n)			{ return (struct arg){ .type = A_VARIABLE, .value = n + 0x01 }; }
static struct arg G(uint8_t n)			{ return (struct arg){ .type = A_VARIABLE, .value = n + 0x10 }; }
static struct arg LBL(const char *n)		{ return (struct arg){ .type = A_JUMP, .jump_type = J_LABEL, .name = xstrdup(n) }; }
static struct arg PCK(const char *n)		{ return (struct arg){ .type = A_JUMP, .jump_type = J_PACKED, .name = xstrdup(n) }; }

static struct arg BRANCH(const char *n, int small)
{
  struct arg arg = { .type = A_JUMP, .jump_type = J_BRANCH, .small = small };

  if(*n == '~')
  {
    arg.invert = 1;
    n++;
  }

  if(*n == '0' || *n == '1') arg.ret = *n - '0';
  else                       arg.name = xstrdup(n);

  return arg;
}

static uint8_t make_type(struct arg arg)
{
  switch(arg.type)
  {
    case A_NONE:
      return 3; /* omitted */

    case A_NUMERIC:
      if(arg.value <= 255) return 1; /* small constant */
      else                 return 0; /* large constant */

    case A_JUMP:
      return 0; /* large constant */

    case A_VARIABLE:
      return 2; /* variable */

    default:
      die("invalid type: %d", (int)arg.type);
  }
}

static void write_arg(struct arg arg)
{
  if(arg.type == A_NONE) return;

  else if(arg.type == A_JUMP) add_jump(arg);

  else switch(make_type(arg))
  {
    case 0: /* large constant */
      WORD(arg.value);
      break;
    case 1: /* small constant */
    case 2: /* variable */
      BYTE(arg.value);
      break;
  }
}

static void make(const struct opcode *op, int znargs, struct arg zargs[], struct arg branch)
{
  uint8_t varbyte = 0xe0;
  int count = op->count;

  /* Special case for a few opcodes.
   * These require the first argument to be a reference to a variable,
   * so a small constant value of 1 would mean local variable 1;
   * however, the user should be able to use L01, SP, etc to refer to
   * them.  Thus rewrite the first argument for these few opcodes.
   */
  if(op->flags & F_INDIRECT)
  {
    zargs[0] = N(zargs[0].value);
  }

  /* @jump takes a label but it doesn’t act like a branch: it’s a 16-bit
   * offset, not 14-bit; the top two bits are not special as they are in
   * branch instructions.  When parsing, ?Foo is treated as a branch,
   * but it should be acceptable to @jump, so rewrite it.
   */
  if(op->flags & F_JUMP)
  {
    BYTE(0x8c);
    branch.jump_type = J_JUMP;
    add_jump(branch);
    return;
  }

  /* @je and @set_colour are both 2OP, but can take a variable number of
   * operands.  If there are not two operands, these should be assembled
   * as a variable VAR would, except the top bits will be 110 instead of
   * 111, indicating 2OP.
   */
  if((op->flags & F_2VAR) && znargs != 2)
  {
    varbyte = 0xc0;
    count = C_VAR;
  }

  /* All 0OP are short */
  if(count == C_ZERO)
  {
    if(znargs != 0) die("0OP called with arguments");

    BYTE(0xb0 | op->number);
  }
  /* All 1OP are short */
  else if(count == C_ONE)
  {
    BYTE(0x80 |
         (make_type(zargs[0]) << 4) |
         op->number
        );
    write_arg(zargs[0]);
  }
  /* 2OP are either long (if no large constant is required) or variable (if one is) */
  else if(count == C_TWO)
  {
    int type1, type2;

    type1 = make_type(zargs[0]);
    type2 = make_type(zargs[1]);

    /* Variable. */
    if(type1 == 0 || type2 == 0)
    {
      BYTE(0xc0 | op->number);
      BYTE( (type1 << 6 ) |
            (type2 << 4 ) |
            0xf
          );
    }
    /* Long. */
    else
    {
      BYTE( ((type1 - 1) << 6) |
            ((type2 - 1) << 5) |
            op->number
          );
    }
    write_arg(zargs[0]);
    write_arg(zargs[1]);
  }
  /* VAR are all variable form */
  else if(count == C_VAR || count == C_EXT)
  {
    struct arg args[8] = { NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE(), NONE() };

    for(int i = 0; i < znargs; i++) args[i] = zargs[i];

    if(count == C_EXT)
    {
      BYTE(0xbe);
      BYTE(op->number);
    }
    else
    {
      BYTE(varbyte | op->number);
    }

    BYTE((make_type(args[0]) << 6) |
         (make_type(args[1]) << 4) |
         (make_type(args[2]) << 2) |
         (make_type(args[3]) << 0));

    if(op->flags & F_DOUBLE)
    {
      BYTE((make_type(args[4]) << 6) |
           (make_type(args[5]) << 4) |
           (make_type(args[6]) << 2) |
           (make_type(args[7]) << 0));
    }

    write_arg(args[0]);
    write_arg(args[1]);
    write_arg(args[2]);
    write_arg(args[3]);

    if(op->flags & F_DOUBLE)
    {
      write_arg(args[4]);
      write_arg(args[5]);
      write_arg(args[6]);
      write_arg(args[7]);
    }
  }

  if(strchr(op->prototype, '>') != NULL) BYTE(zargs[znargs].value); /* guaranteed to be a variable due to the pattern matching */

  if(branch.type == A_JUMP) add_jump(branch);
}

static int stol(const char *s, int base, long *v, long min, long max)
{
  char *endp;

  *v = strtol(s, &endp, base);

  if(endp == s || *endp != 0 || *v < min || *v > max) return 0;

  return 1;
}

static int started = 0;

struct directive
{
  const char *name;
  void (*proc)(int, const char **);
};

static void label_directive(int nargs, const char **args)
{
  if(nargs != 2) die("invalid label syntax");
  if(args[1][0] >= '0' && args[1][0] <= '9') die("label names cannot start with a digit");
  add_label(args[1], TELL());
}

static void alabel_directive(int nargs, const char **args)
{
  SEEKALIGN();
  label_directive(nargs, args);
}

static void routine_directive(int nargs, const char **args)
{
  long val;

  if(nargs < 3) die("invalid routine syntax");
  if(args[1][0] >= '0' && args[1][0] <= '9') die("routine names cannot start with a digit");
  SEEKALIGN();
  add_label(args[1], TELL());
  if(!stol(args[2], 10, &val, 0, 15)) die("invalid number of locals (must be a number between 0 and 15)");
  BYTE(val);

  if(zversion <= 4)
  {
    for(int i = 3; i < nargs; i++)
    {
      long local;

      if(!stol(args[i], 0, &local, INT16_MIN, UINT16_MAX)) die("invalid local (must be a number between %ld and %ld", (long)INT16_MIN, (long)UINT16_MAX);

      WORD(local);

      val--;
    }

    if(val < 0) die("too many local values provided");

    for(long i = 0; i < val; i++) WORD(0);
  }
  else
  {
    if(nargs != 3) die("only V1-4 allow initial local values to be provided");
  }
}

static void byte_directive(int nargs, const char **args)
{
  long val;

  for(int i = 1; i < nargs; i++)
  {
    if(!stol(args[i], 16, &val, 0, 255)) die("invalid byte %s (must be a number between 0x00 and 0xff)", args[i]);
    BYTE(val);
  }
}

static void align_directive(int nargs, const char **args)
{
  if(nargs == 1)
  {
    SEEKALIGN();
  }
  else if(nargs == 2)
  {
    long val;

    if(!stol(args[1], 0, &val, 0, LONG_MAX)) die("invalid alignment %s (must be a positive number)", args[1]);

    SEEK(roundup(TELL(), val), SEEK_SET);
  }
  else
  {
    die("syntax: align [alignment]");
  }
}

static void seek_directive(int nargs, const char **args)
{
  long val;

  if(nargs != 2) die("syntax: seek bytes");
  if(!stol(args[1], 0, &val, 0, max_size())) die("invalid seek %s (must be a positive number less than %lu)", args[1], max_size());
  SEEK(val, SEEK_CUR);
}

static void seeknop_directive(int nargs, const char **args)
{
  long val;
  uint8_t *buffer;

  if(nargs != 2) die("syntax: seeknop bytes");
  if(!stol(args[1], 0, &val, 0, max_size())) die("invalid seek %s (must be a positive number less than %lu)", args[1], max_size());

  /* Try to write the block out in one fell swoop. */
  buffer = malloc(val);
  if(buffer != NULL)
  {
    memset(buffer, 0xb4, val);
    WRITE(buffer, val);
    free(buffer);
  }
  else
  {
    for(long i = 0; i < val; i++) BYTE(0xb4);
  }
}

static void status_directive(int nargs, const char **args)
{
  if(zversion != 3) die("status type can only be set in V3");
  if(nargs != 2) die("syntax: status (score|time)");

  if     (strcmp(args[1], "score") == 0) PBYTE(0x00, 0x01);
  else if(strcmp(args[1], "time")  == 0) PBYTE(0x02, 0x01);
  else                                   die("syntax: status (score|time)");
}

static void start_directive(int nargs, const char **args)
{
  if(started) die("only one start directive can be used");
  started = 1;

  if(TELL() > UINT16_MAX) errx("dynamic memory overflow");

  PWORD(TELL(), 0x04); /* base of high memory */
  PWORD(TELL(), 0x0e); /* overlap static and high for now */

  /* Dictionary. */
  PWORD(TELL(), 0x08);
  BYTE(0x00);
  BYTE(0x06);
  WORD(0x0000);

  /* Temp hack to put packed fuctions above address 255 */
  SEEK(0x3450, SEEK_SET);

  /* Packed address of initial routine (V6) or initial PC value (otherwise). */
  if(zversion == 6)
  {
    SEEKALIGN();
    PWORD(pack(TELL()), 0x06);
    routine_directive(nargs, args);
  }
  else
  {
    PWORD(TELL(), 0x06);
  }
}

#define DIRECTIVE(name_)	{ .name = #name_, .proc = name_##_directive }

static const struct directive directives[] =
{
  DIRECTIVE(label),
  DIRECTIVE(alabel),
  DIRECTIVE(routine),
  DIRECTIVE(byte),
  DIRECTIVE(align),
  DIRECTIVE(seek),
  DIRECTIVE(seeknop),
  DIRECTIVE(status),
  DIRECTIVE(start),

  { NULL },
};

#undef DIRECTIVE

static void parse_args(int nargs, const char **args)
{
  int n = 0;
  char prototype[nargs];
  int znargs = 0;
  struct arg zargs[nargs];
  struct arg branch = NONE();
  const struct opcode *op;
  long val;

  for(size_t i = 0; i < ASIZE(zargs); i++) zargs[i] = NONE();

  for(op = opcodes; op->name != NULL; op++)
  {
    if(strcmp(op->name, args[0]) == 0) break;
  }

  if(op->name == NULL)
  {
    const struct directive *dir;

    for(dir = directives; dir->name != NULL; dir++)
    {
      if(strcmp(dir->name, args[0]) == 0) break;
    }

    if(dir->name == NULL) die("invalid instruction: %s", args[0]);
    
    dir->proc(nargs, args);

    return;
  }

  for(int i = 1; i < nargs; i++)
  {
    if(strcmp(args[i], "sp") == 0 || strcmp(args[i], "SP") == 0)
    {
      prototype[n++] = 'v';
      zargs[znargs++] = SP();
    }
    else if(args[i][0] == 'G')
    {
      prototype[n++] = 'v';
      if(!stol(&args[i][1], 16, &val, 0, 239)) die("invalid global %s (must be a number between 0x00 and 0xef)", args[i]);
      zargs[znargs++] = G(val);
    }
    else if(args[i][0] == 'L')
    {
      prototype[n++] = 'v';
      if(!stol(&args[i][1], 10, &val, 0, 15)) die("invalid local %s (must be a number between 0 and 15)", args[i]);
      zargs[znargs++] = L(val);
    }
    else if(args[i][0] == '?')
    {
      prototype[n++] = '?';
      branch = BRANCH(&args[i][1], 0);
    }
    else if(args[i][0] == '%')
    {
      prototype[n++] = '?';
      branch = BRANCH(&args[i][1], 1);
    }
    else if(args[i][0] == '!')
    {
      prototype[n++] = 'n';
      zargs[znargs++] = PCK(&args[i][1]);
    }
    else if(args[i][0] == '&')
    {
      prototype[n++] = 'n';
      zargs[znargs++] = LBL(&args[i][1]);
    }
    else if(strcmp(args[i], "->") == 0)
    {
      prototype[n++] = '>';
    }
    else
    {
      if(!stol(args[i], 0, &val, LONG_MIN, LONG_MAX)) die("syntax error: %s", args[i]);

      if(val < INT16_MIN || val > UINT16_MAX) die("number out of range: must be in the range %ld to %ld", (long)INT16_MIN, (long)UINT16_MAX);

      zargs[znargs++] = N(val);

      prototype[n++] = 'n';
    }
  }

  prototype[n] = 0;

  /* If there is a store, don't count the target variable as an
   * argument, because it's not one.  In the case of a store,
   * zargs[znargs] will be the variable in which to store.
   */
  if(strchr(prototype, '>') != NULL) znargs--;

  if(regexec(&op->re, prototype, 0, NULL, 0) != 0) die("no matching pattern: expected %s, found %s", op->prototype, prototype);

  make(op, znargs, zargs, branch);

  for(size_t i = 0; i < ASIZE(zargs); i++) free(zargs[i].name);

  free(branch.name);
}

static uint8_t atable[26 * 3] =
{
  /* A0 */
  'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
  'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',

  /* A1 */
  'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
  'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',

  /* A2 */
  0x0, '^', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '.',
  ',', '!', '?', '_', '#', '\'','"', '/', '\\','-', ':', '(', ')',
};

static long etable_unicode_addr;

static int in_atable(int c)
{
  /* 52 is A2 character 6, which is special and should not be matched,
   * so skip over it.
   */
  for(int i = 0;  i < 52    ; i++) if(atable[i] == c) return i;
  for(int i = 53; i < 26 * 3; i++) if(atable[i] == c) return i;

  return -1;
}

/* Encode a string, passing each Z-character (and its index) to “cb”. */
static int encode_string_backend(const uint16_t *s, size_t len, void (*cb)(uint16_t, int))
{
  const int shiftbase = zversion <= 2 ? 1 : 3;
  int n = 0;

  for(size_t i = 0; i < len; i++)
  {
    int pos = in_atable(s[i]);

    if(zversion == 1 && s[i] == '^')
    {
      cb(1, n++);
    }
    else if(pos >= 0)
    {
      int shift = pos / 26;
      int c = pos % 26;

      if(shift) cb(shiftbase + shift, n++);
      cb(c + 6, n++);
    }
    else if(s[i] == ' ')
    {
      cb(0, n++);
    }
    else
    {
      cb(shiftbase + 2, n++);
      cb(6, n++);

      if(s[i] > 126)
      {
        uint8_t c = unicode_to_zscii(s[i]);

        cb(c >> 5, n++);
        cb(c & 0x1f, n++);
      }
      else
      {
        cb(s[i] >> 5, n++);
        cb(s[i] & 0x1f, n++);
      }
    }
  }

  /* Pad */
  while(n == 0 || (n % 3) != 0) cb(5, n++);

  /* Convert Z-character count to bytes. */
  return 2 * (n / 3);
}

/* Stub function, used to calculate how long an encoded string will be. */
static void encode_length_cb(uint16_t c, int n)
{
}

static uint16_t GET_WORD(uint8_t *base)
{
  return (base[0] << 8) | base[1];
}
static void MAKE_WORD(uint8_t *base, uint16_t val)
{
  base[0] = val >> 8;
  base[1] = val & 0xff;
}

static uint8_t *encoded;
static void encode_string_cb(uint16_t c, int n)
{
  uint16_t w = GET_WORD(&encoded[2 * (n / 3)]);

  w |= (c & 0x1f) << (5 * (2 - (n % 3)));

  MAKE_WORD(&encoded[2 * (n / 3)], w);
}
static int encode_string(const uint16_t *s, size_t len)
{
  int enclen;

  free(encoded);

  enclen = encode_string_backend(s, len, encode_length_cb);
  encoded = calloc(enclen, 1);
  if(encoded == NULL) err("calloc");

  encode_string_backend(s, len, encode_string_cb);

  /* Mark the end */
  encoded[enclen - 2] |= 0x80;

  WRITE(encoded, enclen);

  return enclen;
}

static int print_handler(const char *string)
{
  uint16_t utf[strlen(string)];
  size_t n;

  n = decode_utf8(string, utf);

  return encode_string(utf, n);
}

/* Write out an object name, which is a byte describing how long the
 * (encoded) name is, followed by the encoded name.
 */
static void object_name(const char *name)
{
  int bytes;

  BYTE(0); /* placeholder for text-length */
  bytes = print_handler(name);
  if(bytes > 255) die("object name too long");
  PBYTE(bytes, TELL() - bytes - 1); /* write text-length */
}

static void start_file(const char *filename)
{
  fd = open(filename, O_RDWR | O_CREAT | O_TRUNC, 0644);
  if(fd == -1) err("out.z5");

  /* Zero the header out. */
  for(int i = 0; i < 64; i++) PBYTE(0x00, i);

  PBYTE(zversion, 0x00);   /* version */
  PWORD(release, 0x02);    /* release */
  PWRITE(serial, 6, 0x12); /* serial number */

  /* Alphabet table. */
  SEEK(0x40, SEEK_SET);
  PWORD(TELL(), 0x34);
  WRITE(atable, 26 * 3);

  /* Header extension table. */
  if(zversion >= 5)
  {
    PWORD(TELL(), 0x36);
    WORD(0x0003);
    WORD(0x0000);
    WORD(0x0000);
    etable_unicode_addr = TELL();
    WORD(0x0000);
  }

  /* Globals. */
  PWORD(TELL(), 0x0c);

  /* The first global needs to be set to a valid object for show_status;
   * point it to the default object.  In the future, when objects are
   * fully supported, this should be configurable by the user.
   */
  if(zversion <= 3)
  {
    WORD(0x0001);
    SEEK(478, SEEK_CUR);
  }
  else
  {
    SEEK(480, SEEK_CUR);
  }

  /* Property defaults table. */
  PWORD(TELL(), 0x0a);
  SEEK(zversion <= 3 ? 62 : 126, SEEK_CUR);

  if(zversion == 6 || zversion == 7)
  {
    PWORD(0x0000, 0x28); /* Routines offset. */
    PWORD(0x0000, 0x2a); /* Static strings offset. */
  }

  /* Object table (just one object is created for now). */
  PWORD(TELL(), 0x0a);

  /* Object 1. */
  if(zversion <= 3)
  {
    for(int i = 0; i < 31; i++) WORD(0x0000); /* Property defaults table. */
    for(int i = 0; i <  2; i++) WORD(0x0000); /* Attribute flags. */
    for(int i = 0; i <  3; i++) BYTE(0x00);   /* Parent, sibling, child. */
    WORD(TELL() + 2); /* Properties. */
  }
  else
  {
    for(int i = 0; i < 63; i++) WORD(0x0000); /* Property defaults table. */
    for(int i = 0; i <  3; i++) WORD(0x0000); /* Attribute flags. */
    for(int i = 0; i <  3; i++) WORD(0x0000); /* Parent, sibling, child. */
    WORD(TELL() + 2); /* Properties. */
  }

  /* Property table (just the name and a terminating marker). */
  object_name("Default object");
  BYTE(0);
}

static void end_file(void)
{
  ssize_t n;
  size_t file_size;
  unsigned char buf[8192];
  uint16_t checksum = 0;

  /* Unicode table. */
  if(unicode_index != 0)
  {
    PWORD(TELL(), etable_unicode_addr);
    BYTE(unicode_index);
    for(int i = 0; i < unicode_index; i++) WORD(unicode_table[i]);
  }

  if(zversion >= 3)
  {
    SEEK(0x40, SEEK_SET);
    file_size = 0x40;
    while((n = read(fd, buf, sizeof buf)) > 0)
    {
      for(ssize_t i = 0; i < n; i++) checksum += buf[i];

      file_size += n;
    }

    if(n < 0) err("read");

    for(size_t i = 0; i < ALIGN(file_size) - file_size; i++) BYTE(0);
    file_size = ALIGN(file_size);

    if(file_size > max_size()) errx("file size too large (%zu)", file_size);

    PWORD(file_size / (zversion == 3 ? 2 : zversion <= 5 ? 4 : 8), 0x1a);
    PWORD(checksum, 0x1c);
  }

  close(fd);
}

static void process_file(FILE *fp, const char *fn)
{
  char buf[sizeof current_line];
  int saved_lineno;

  current_file = fn;
  current_lineno = 0;

  while(fgets(buf, sizeof buf, fp) != NULL)
  {
    char *p;
    int i;
    const char *args[32];

    *current_line = 0;
    current_lineno++;

    p = strchr(buf, '\n');
    if(p == NULL) die("no newline; line too long?");
    *p = 0;

    strcpy(current_line, buf);

    p = strchr(buf, '#');
    if(p != NULL) *p = 0;

    if(buf[0] == 0) continue;

    /* @print and @print_ret must be handled here, before tokenization,
     * because spaces are significant.  The string directive is similar.
     */
    if(strncmp(buf, "print ", 6) == 0)
    {
      BYTE(0xb2);
      print_handler(strchr(buf, ' ') + 1);
      continue;
    }

    if(strncmp(buf, "print_ret ", 10) == 0)
    {
      BYTE(0xb3);
      print_handler(strchr(buf, ' ') + 1);
      continue;
    }

    if(strncmp(buf, "string ", 7) == 0)
    {
      SEEKALIGN();
      print_handler(strchr(buf, ' ') + 1);
      continue;
    }

    p = strtok(buf, " \t");

    /* This does NOT detect recursion! */
    if(strcmp(p, "include") == 0)
    {
      const char *file = strtok(NULL, "");
      FILE *fp2;

      if(file == NULL) die("bad line");

      fp2 = fopen(file, "r");
      if(fp2 == NULL) die("fopen: %s", strerror(errno));

      saved_lineno = current_lineno;

      process_file(fp2, file);

      fclose(fp2);

      current_file = fn;
      current_lineno = saved_lineno;

      continue;
    }

    i = 0;
    args[i++] = p;

    for(p = strtok(NULL, " \t"); p != NULL; p = strtok(NULL, " \t"))
    {
      if(i == ASIZE(args)) die("too many tokens");
      args[i++] = p;
    }

    parse_args(i, args);
  }

  if(!started) errx("no start directive found");
}

int main(int argc, char **argv)
{
  int c;
  const char *infile, *outfile = "out.z5";
  FILE *fp;

  if(strftime(serial, sizeof serial, "%y%m%d", localtime(&(time_t){ time(NULL) })) != 6) strcpy(serial, "000000");

  while((c = getopt(argc, argv, "o:r:s:v:")) != -1)
  {
    switch(c)
    {
      case 'o':
        outfile = optarg;
        break;
      case 'r':
        if(!stol(optarg, 10, &release, 0, UINT16_MAX)) errx("release must be a number from 0 to %lu", (unsigned long)UINT16_MAX);
        break;
      case 's':
        if(strlen(optarg) != 6) errx("serial number must be a six-digit string");
        strcpy(serial, optarg);
        break;
      case 'v':
        if(!stol(optarg, 10, &zversion, 1, 8)) errx("invalid z-machine version: must be 1 to 8");
        break;
      default:
        exit(1);
    }
  }

  if(zversion == 1) memcpy(&atable[26 * 2], " 0123456789.,!?_#'\"/\\<-:()", 26);

  if(argc <= optind) exit(1);

  infile = argv[optind];

  setup_opcodes();

  start_file(outfile);

  fp = fopen(infile, "r");
  if(fp == NULL) err("%s", infile);

  process_file(fp, infile);

  fclose(fp);

  apply_jumps();

  end_file();

  return 0;
}
