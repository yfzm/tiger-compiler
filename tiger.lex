%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "y.tab.h"
#include "errormsg.h"

int charPos=1;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
char esp_char[] = "nt\\";
char a_esp_char[] = "\n\t\\";
int is_space(char c) {
  if (c == ' ' || c == '\n' || c == '\t' || c == '\v' || c == '\f' || c == '\r') 
    return 1;
  return 0;
}
char *getstr(const char *str)
{
  //printf(">>>>>%s(%d)<<<<<\n", str, strlen(str));
  if (strlen(str) <= 2) return NULL;
  char *dst = (char *)malloc(yyleng);
  int ini = 1, outi = 0, n = 0;
  for (; ini < yyleng - 1; ini++) {
    if (str[ini] == '\\') {
      if (str[ini+1] >= '0' && str[ini+1] <= '9' && str[ini+2] >= '0' && str[ini+2] <= '9' && str[ini+3] >= '0' && str[ini+3] <= '9') {
        int num = (str[ini+1] - '0') * 100 + (str[ini+2] - '0') * 10 + (str[ini+3] - '0');
        dst[outi++] = (char)(num);
        ini+=3;
        continue;
      }
      if (str[ini+1] == '\\') {
        dst[outi++] = '\\';
        ini++;
        continue;
      }
      if (str[ini+1] == '^') {
        if (str[ini+2] >= 'A' && str[ini+2] <= 'Z') {
          dst[outi++] = str[ini+2] - 'A' + 1;
          ini += 2;
          continue;
        } else {
          free(dst);
          EM_error(EM_tokPos, "illegal string");
        }
      }
      if (is_space(str[ini+1]) == 1) {
        while (ini + 1 < yyleng - 1) {
          if (str[ini+1] == '\\') { ini++; break; }
          if (is_space(str[ini+1]) == 1) { ini++; continue; }
          EM_error(EM_tokPos, "illegal string");
        }
      }
      for (int i = 0; i < strlen(esp_char); i++) {
        // printf("%c", esp_char[i]);
        if (str[ini+1] == esp_char[i]) {
          dst[outi++] = a_esp_char[i];
          ini++;
          break;
        }
        if (ini+1 == yyleng-1) {
          free(dst);
          EM_error(EM_tokPos, "illegal string");
        }
      }
    } else {
      dst[outi++] = str[ini];
    }
  }
  dst[outi] = '\0';

  return dst;
}

int comment_count = 0;

%}
  /* You can add lex definitions here. */
digit    [0-9]
letter   [a-zA-Z]
char     [0-9a-zA-Z_]
space    [ \t\f\r\v]

%START COMMENT
%%

<INITIAL>{space}   {adjust(); continue;}
<INITIAL>\n        {adjust(); EM_newline(); continue;}
<INITIAL>","       {adjust(); return COMMA;}
<INITIAL>":"       {adjust(); return COLON;}
<INITIAL>";"       {adjust(); return SEMICOLON;}
<INITIAL>"("       {adjust(); return LPAREN;}
<INITIAL>")"       {adjust(); return RPAREN;}
<INITIAL>"["       {adjust(); return LBRACK;}
<INITIAL>"]"       {adjust(); return RBRACK;}
<INITIAL>"{"       {adjust(); return LBRACE;}
<INITIAL>"}"       {adjust(); return RBRACE;}
<INITIAL>"."       {adjust(); return DOT;}
<INITIAL>"+"       {adjust(); return PLUS;}
<INITIAL>"-"       {adjust(); return MINUS;}
<INITIAL>"*"       {adjust(); return TIMES;}
<INITIAL>"/"       {adjust(); return DIVIDE;}
<INITIAL>"="       {adjust(); return EQ;}
<INITIAL>"<>"      {adjust(); return NEQ;}
<INITIAL>"<"       {adjust(); return LT;}
<INITIAL>"<="      {adjust(); return LE;}
<INITIAL>">"       {adjust(); return GT;}
<INITIAL>">="      {adjust(); return GE;}
<INITIAL>"&"       {adjust(); return AND;}
<INITIAL>"|"       {adjust(); return OR;}
<INITIAL>":="      {adjust(); return ASSIGN;}

<INITIAL>for  	   {adjust(); return FOR;}
<INITIAL>while     {adjust(); return WHILE;}
<INITIAL>to        {adjust(); return TO;}
<INITIAL>break     {adjust(); return BREAK;}
<INITIAL>let       {adjust(); return LET;}
<INITIAL>in        {adjust(); return IN;}
<INITIAL>end       {adjust(); return END;}
<INITIAL>function  {adjust(); return FUNCTION;}
<INITIAL>var       {adjust(); return VAR;}
<INITIAL>type      {adjust(); return TYPE;}
<INITIAL>array     {adjust(); return ARRAY;}
<INITIAL>if        {adjust(); return IF;}
<INITIAL>then      {adjust(); return THEN;}
<INITIAL>else      {adjust(); return ELSE;}
<INITIAL>do        {adjust(); return DO;}
<INITIAL>of        {adjust(); return OF;}
<INITIAL>nil       {adjust(); return NIL;}

<INITIAL>{digit}+           {adjust(); yylval.ival=atoi(yytext); return INT;}
<INITIAL>{letter}{char}*    {adjust(); yylval.sval=String(yytext); return ID;}

<INITIAL>"/*"               {adjust(); comment_count = 1; BEGIN COMMENT;}
<INITIAL>\"(\\.|[^"])*\"  {adjust(); yylval.sval=getstr(yytext); /*if (yylval.sval == NULL) { EM_error(EM_tokPos, "illegal string"); }*/ return STRING; }
<INITIAL>.         {adjust(); EM_error(EM_tokPos, "illegal character");}

<COMMENT>"/*"      {adjust(); comment_count++; continue;}
<COMMENT>"*/"      {adjust(); if (--comment_count == 0) BEGIN INITIAL; else continue;}
<COMMENT>\n        {adjust(); EM_newline(); continue;}
<COMMENT>.         {adjust(); continue;}

<COMMENT><<EOF>>   {if (comment_count!=0) { EM_error(EM_tokPos, "EOF: missing matched TERMINATE COMMENT"); yyterminate();} }
