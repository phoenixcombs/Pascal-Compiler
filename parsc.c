/* parsc.c    Pascal Parser      Gordon S. Novak Jr.    02 Nov 05    */

/* This file contains a parser for a Pascal subset using the techniques of
   recursive descent and operator precedence.  The Pascal subset is equivalent
   to the one handled by the Yacc version pars1.y .  */

/* Copyright (c) 2005 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */


/* To use:
                     make pars1c
                     pars1c
                     i:=j .

                     pars1c
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.

                     pars1c
                     if x+y then if y+z then i:=j else k:=2.
                     if x-y then if y+z then i:=j else k:=2.
*/

/* You may copy this file to be parsc.c, expand it for your assignment,
   then use    make parsec    as above.  */

#include <stdio.h>
#include <ctype.h>
#include "token.h"
#include "lexan.h"
#include "symtab.h"
#include "parse.h"

int bin = 1;
int multvar = 1;
int real = 0;
int begin = 0;
int labelnum = 0;
int symTableInit = 0;
int position = 0;
int labelpos = 0;
SYMBOL unlinked[10];
TOKEN unlinkedname[10];
TOKEN labelnames[10];
TOKEN labeltokens[10];
TOKEN parseresult;
TOKEN savedtoken;
#define DEBUG        0//127             /* set bits here for debugging, 0 = off  */
#define DB_CONS       1             /* bit to trace cons */
#define DB_BINOP      2             /* bit to trace binop */
#define DB_MAKEIF     4             /* bit to trace makeif */
#define DB_MAKEPROGN  8             /* bit to trace makeprogn */
#define DB_PARSERES  16             /* bit to trace parseresult */
#define DB_GETTOK    32             /* bit to trace gettok */
#define DB_EXPR      64             /* bit to trace expr */

TOKEN cons(TOKEN item, TOKEN list)           /* add item to front of list */
{
    item->link = list;
    if (DEBUG & DB_CONS)
    {
        printf("cons\n");
        dbugprinttok(item);
        dbugprinttok(list);
    };
    return item;
}

/*Copied in with instvars*/
int wordaddress(int n, int wordsize)
{
    return ((n + wordsize - 1) / wordsize) * wordsize;
}

/* install variables in symbol table */
void instvars(TOKEN idlist, TOKEN typetok)
{
    SYMBOL sym, typesym; int align;
    if (DEBUG)
    {
        printf("instvars\n");
        dbugprinttok(idlist);
        dbugprinttok(typetok);
    };
    typesym = typetok->symtype;
    align = alignsize(typesym);
    while ( idlist != NULL )   /* for each id */
    {
        sym = insertsym(idlist->stringval);
        sym->kind = VARSYM;
        sym->offset = wordaddress(blockoffs[blocknumber], align);
        sym->size = typesym->size;
        blockoffs[blocknumber] = sym->offset + sym->size;
        sym->datatype = typesym;
        sym->basicdt = typesym->basicdt; /* some student programs use this */
          idlist = idlist->link;
    };
    if (DEBUG) printst();
}

/* instconst installs a constant in the symbol table */
void instconst(TOKEN idtok, TOKEN consttok)
{
    SYMBOL sym, typesym; int align;
    if (DEBUG)
    {
        printf("instconst\n");
        dbugprinttok(idtok);
        dbugprinttok(consttok);
    };
    //typesym = consttok->symtype;
    align = alignsize(typesym);
    sym = insertsym(idtok->stringval);
    sym->kind = CONSTSYM;
    sym->offset = wordaddress(blockoffs[blocknumber], align);
    sym->size = typesym->size;
    blockoffs[blocknumber] = sym->offset + sym->size;
    sym->datatype = typesym;
    sym->basicdt = consttok->datatype; /* some student programs use this */
    if(consttok->datatype == 0)
        sym->constval.intnum = consttok->intval;
    else
        sym->constval.realnum = consttok->realval;
    if (DEBUG) printst();
}

/* Finds the token in the symbol table, and replaces the value if it is constant */
TOKEN lookup(TOKEN tok)
{
    SYMBOL sym, typ;
    sym = searchst(tok->stringval);
    if(sym != NULL)
    {
        if(sym->kind == CONSTSYM)
        {
            tok->tokentype = NUMBERTOK;
            tok->datatype = sym->basicdt;
            if(tok->datatype == INTEGER)
                tok->intval = sym->constval.intnum;
            else if(tok->datatype == REAL)
                tok->realval = sym->constval.realnum;
        }
        else if(sym->kind == VARSYM)
        {
            tok->symentry = sym;
            typ = sym->datatype;
            tok->symtype = typ;
            if(typ->kind == BASICTYPE || typ->kind == POINTERSYM)
                tok->datatype = typ->basicdt;
        }
        return tok;
    }
    else
    {
        return NULL;
    }
}

TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs)       /* reduce binary operator */
{            /* operator, left-hand side, right-hand side */
    op->operands = lhs;         /* link operands to operator       */
    lhs->link = rhs;            /* link second operand to first    */
    rhs->link = NULL;           /* terminate operand list          */
    if (DEBUG & DB_BINOP)
    {
        printf("binop\n");
        dbugprinttok(op);      /*       op         =  (op lhs rhs)      */
        dbugprinttok(lhs);     /*      /                                */
        dbugprinttok(rhs);     /*    lhs --- rhs                        */
    };
    return op;
}

/* Same as binop, except fr unary ops, such as (-x)*/
TOKEN unaryop(TOKEN op, TOKEN lhs)
{
    op->operands = lhs;         /* link operands to operator       */
    lhs->link = NULL;           /* terminate operand list          */
    if (DEBUG & DB_BINOP)
    {
        printf("unaryop\n");
        dbugprinttok(op);      /*       op         =  (op lhs)          */
                               /*      /                                */
        dbugprinttok(lhs);     /*    lhs                                */
    };
    return op;
}

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart)
{
    tok->tokentype = OPERATOR;  /* Make it look like an operator   */
    tok->whichval = IFOP;
    if(elsepart != NULL)
        elsepart->link = NULL;
    thenpart->link = elsepart;
    exp->link = thenpart;
    tok->operands = exp;
    if(DEBUG & DB_MAKEIF)
    {
        printf("makeif\n");
        dbugprinttok(tok);
        dbugprinttok(exp);
        dbugprinttok(thenpart);
        dbugprinttok(elsepart);
    };
    return tok;
}

/*Returns a Token with the value of value*/
TOKEN getnumbertok(int value)
{
    TOKEN numtok = talloc();
    numtok->tokentype = NUMBERTOK;
    numtok->datatype = INTEGER;
    numtok->whichval = value;
    return numtok;
}

/*Returns a GOTO Token with the operand of value*/
TOKEN makegoto(int label)
{
    TOKEN gototok = talloc();
    gototok->tokentype = OPERATOR;
    gototok->whichval = GOTOOP;
    gototok->operands = getnumbertok(label);
    return gototok;
}

/*Returns a LABEL Token with the labelnum as the operand */
TOKEN makelabel()
{
    TOKEN label = talloc();
    label->tokentype = OPERATOR;
    label->whichval = LABELOP;
    label->operands = getnumbertok(labelnum);
    labelnum = labelnum + 1;
    return label;
}

/*Generates a tree for a for loop*/
TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr, TOKEN tokc, TOKEN statements)
{
    TOKEN label = makelabel();
    TOKEN increment = talloc();
    TOKEN copy;
    increment->tokentype = OPERATOR;
    tokb->tokentype = OPERATOR;
    if(sign > 0)
    {
        tokb->whichval = LEOP;
        increment->whichval = PLUSOP;
    }
    else if(sign < 0)
    {
        tokb->whichval = GEOP;
        increment->whichval = MINUSOP;
    }
    makeprogn(tok, asg);
    tokb->operands = copytok(asg->operands);
    tokb->operands->link = endexpr;
    tokc->tokentype = OPERATOR;
    tokc->whichval = ASSIGNOP;
    asg->link = label;
    copy = copytok(asg->operands);
    statements->link = binop(tokc, copy, binop(increment, copytok(asg->operands), getnumbertok(1)));
    statements->link->link = makegoto(label->operands->whichval);
    label->link = makeif(talloc(), tokb, makeprogn(talloc(), statements), NULL);
    return tok;
}

/*Creates a copy of a token
  Allowing it to be changed,
  And not alter the original*/
TOKEN copytok(TOKEN origtok)
{
    TOKEN newtok = talloc();
    int i;
    for(i = 0; i < 16; i++)
    {
        newtok->stringval[i] = origtok->stringval[i];
    }
    newtok->tokentype = origtok->tokentype;
    newtok->datatype  = origtok->datatype;
    newtok->whichval  = origtok->whichval;
    newtok->operands  = origtok->operands;
    newtok->link = origtok->link;
    newtok->symtype = origtok->symtype;
    newtok->symentry = origtok->symentry;
    return newtok;
}

/*Generates the tree for a Program*/
TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN statements)
{
    TOKEN statement();
    name->tokentype = OPERATOR;  /* Make it look like an operator   */
    name->whichval = PROGRAMOP;
    statements->link = statement();
    args->link = statements;
    name->operands = args;
    if(DEBUG & DB_MAKEPROGN)
    {
        printf("makeprogram\n");
        dbugprinttok(name);
        dbugprinttok(args);
        dbugprinttok(statements);
    };
    return name;
}

/*Generates the tree for a Function Call*/
TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args)
{
    fn->tokentype = OPERATOR;
    fn->whichval = FUNCALLOP;
    fn->operands = tok;
    tok->link = args;
    return fn;
}

/*Genrates the tree for a Repeat*/
TOKEN makerepeat(TOKEN tok, TOKEN statements, TOKEN tokb, TOKEN expr)
{
    /*
        tok = repeat
        statements = write(' ')
        tokb = until
        expr = n := n - 1
    */
    TOKEN label = talloc();
    TOKEN parseexpr();
    TOKEN gototok = talloc();
    label = makelabel();
    makeprogn(tok, label);
    label->link = statements;
    statements->link = expr;
    tokb->tokentype = OPERATOR;
    tokb->whichval = IFOP;
    tokb->operands = parseexpr();
    gototok = makegoto(label->operands->whichval);
    tokb->operands->link = makeprogn(copytok(tok), NULL);
    tokb->operands->link->link = gototok;
    expr->link = tokb;
    return tok;
}

/*Generates the tree for a progn*/
TOKEN makeprogn(TOKEN tok, TOKEN statements)
{
    tok->tokentype = OPERATOR;
    tok->whichval = PROGNOP;
    tok->operands = statements;
    if(DEBUG & DB_MAKEPROGN)
    {
        printf("makeprogn\n");
        dbugprinttok(tok);
        dbugprinttok(statements);
    };
    return tok;
}

yyerror(s)
  char * s;
  { 
  fputs(s,stderr); putc('\n',stderr);
  }

TOKEN gettok()       /* Get the next token; works with peektok. */
{
    TOKEN tok;
    if(savedtoken != NULL)
    {
        tok = savedtoken;
          savedtoken = NULL;
    }
    else
        tok = gettoken();
    if(DEBUG & DB_GETTOK)
    {
        printf("gettok\n");
        dbugprinttok(tok);
    };
    return(tok);
}

TOKEN peektok()       /* Peek at the next token */
{
    if(savedtoken == NULL)
        savedtoken = gettoken();
    if(DEBUG & DB_GETTOK)
    {
        printf("peektok\n");
        dbugprinttok(savedtoken);
    };
    return(savedtoken);
}

int reserved(TOKEN tok, int n)          /* Test for a reserved word */
{
    return (tok->tokentype == RESERVED && (tok->whichval + RESERVED_BIAS ) == n);
}

TOKEN parsebegin(TOKEN keytok)  /* Parse a BEGIN ... END statement */
{
    TOKEN front, end, tok;
    TOKEN statement();
    int done;
    int state;
    int loop;
    state = 1;
    loop = 1;
    front = NULL;
    done = 0;
    while(done == 0)
    {
        if(peektok()->tokentype == RESERVED && peektok()->whichval + RESERVED_BIAS == FOR && loop)
            state = 0;
        loop = 0;
        tok = statement();        /* Get a statement */
        if(front == NULL)      /* Put at end of list */
            front = tok;
        else
            end->link = tok;
        tok->link = NULL;
        end = tok;
        tok = peektok();
        tok = gettok();           /* Get token: END or semicolon */
        if(reserved(tok, END))
            done = 1;
        else if(tok->tokentype != DELIMITER || (tok->whichval + DELIMITER_BIAS) != SEMICOLON)
            yyerror("Bad item in begin - end.") ;
    };
    if(state)
        return (makeprogn(keytok,front));
    else
        return (front);
}

/* Parses a Repeat statement, and throws an error in no Until */
TOKEN parserepeat(TOKEN keytok)
{
    TOKEN statements, tok, expr;
    TOKEN statement();
    TOKEN parseexpr();
    statements = parseexpr();
    tok = gettok();
    expr = statement();
    tok = gettok();           /* Get token: UNTIL */
    if(reserved(tok, UNTIL) == 0)
        yyerror("Missing UNTIL");
    return (makerepeat(keytok, statements, tok, expr));
}

TOKEN parseprogram(TOKEN keytok)  /* Parse a PROGRAM statement */
{
    TOKEN expr, tok, args;
    TOKEN parseexpr();
    tok = gettok();
    args = peektok();
    expr = parseexpr();
    makeprogn(args, expr);
    gettok();
    return (makeprogram(keytok, tok, args));
}

/* makewhile makes structures for a while statement.
   tok and tokb are (now) unused tokens that are recycled. */
TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement)
{
    TOKEN label = talloc();
    TOKEN tmp = talloc();
    TOKEN gototok = talloc();
    label = makelabel();
    gototok = makegoto(label->operands->intval);
    tmp = statement->operands;
    while(tmp->link != NULL)
    {
        tmp = tmp->link;
    }
    tmp->link = gototok;
    label->link = makeif(talloc(), expr, makeprogn(talloc(), statement), NULL);
    return makeprogn(tokb, label);
}

TOKEN parsewhile(TOKEN keytok)
{
    TOKEN tokb = talloc();
    TOKEN expr = talloc();
    TOKEN statements = talloc();
    TOKEN statement();
    TOKEN parseexpr();
    expr = parseexpr();
    tokb = gettok();
    if(reserved(tokb, DO) == 0)
        yyerror("MISSING DO");
    statements = statement();
    return makewhile(keytok, expr, tokb, statements);
}

/* Added code to check the data types of the assignee and the operands */
TOKEN parsefuncall(TOKEN tok)        /* Parse a FUNCTION CALL */
{
    TOKEN fn = talloc();
    TOKEN args = talloc();
    TOKEN holder = talloc();
    TOKEN holder2 = talloc();
    TOKEN parseexpr();
    SYMBOL sym;
    args = parseexpr();
    sym = searchst(tok->stringval);
    if(sym != NULL)
    {
        if(sym == searchst("new"))
        {
            holder->tokentype = OPERATOR;
            holder->whichval = ASSIGNOP;
            holder2->tokentype = OPERATOR;
            holder2->whichval = FUNCALLOP;
            holder2 = binop(copytok(holder2), tok, getnumbertok(searchst(args->stringval)->datatype->link->size));
            return binop(copytok(holder), args, copytok(holder2));
        }
        if(sym->datatype->link->datatype->basicdt == REAL)
        {
            real = 1;
            holder = copytok(args->operands);
            sym = searchst(holder->stringval);
            if(sym != NULL && sym->datatype->basicdt == INTEGER && holder->tokentype != 0)
            {
                holder2->tokentype = OPERATOR;
                holder2->whichval = FLOATOP;
                unaryop(holder2, copytok(holder));
                holder2->link = args->operands->link;
                args->operands = copytok(holder2);
            }
            else if(holder->tokentype == NUMBERTOK && holder->datatype == INTEGER && holder->tokentype != 0)
            {
                holder2 = args->operands->link;
                args->operands->datatype = REAL;
                args->operands->realval = holder->intval*1.0;
                args->operands->link = copytok(holder2);
            }
            if(args->operands->link != NULL)
            {
                holder = copytok(args->operands->link);
                sym = searchst(holder->stringval);
                if(sym != NULL && sym->datatype->basicdt == INTEGER && holder->tokentype != 0)
                {
                    holder2->tokentype = OPERATOR;
                    holder2->whichval = FLOATOP;
                    unaryop(holder2, holder);
                    args->operands->link = copytok(holder2);
                }
                else if(sym != NULL && sym->datatype->basicdt == REAL && holder->tokentype != 0)
                {
                }
                else if(holder->datatype == INTEGER && holder->tokentype != 0)
                {
                    args->operands->link->realval = holder->intval*1.0;
                    args->operands->link->datatype = REAL;
                }
            }
        }
    }
    return (makefuncall(tok, fn, args));
}

/*
    sign is 1 for normal loop, -1 for downto.
    asg is an assignment statement, e.g. (:= i 1)
    endexpr is the end expression
*/
TOKEN parsefor(TOKEN keytok)        /* Parse a FOR statement */
{
    TOKEN asg, tokb, endexpr, tokc, statements;
    TOKEN parseexpr();
    TOKEN statement();
    int sign;
    sign = 0;
    asg = parseexpr();
    tokb = gettok();
    if(reserved(tokb, TO) == 1)
        sign = 1;
    else if(reserved(tokb, DOWNTO) == 1)
        sign = -1;
    else
        yyerror("Missing TO/DOWNTO");
    endexpr = gettok();
    tokc = lookup(endexpr);
    if(tokc != NULL)
        endexpr = copytok(tokc);
    tokc = gettok();
    if(reserved(tokc, DO) == 0)
        yyerror("Missing DO");
    statements = statement();
    return (makefor(sign, keytok, asg, tokb, endexpr, tokc, statements));
}

/* Parse a VAR statement add to the symbol table */
TOKEN parsevar(TOKEN keytok)
{
    if(DEBUG & DB_MAKEPROGN)
    {
        printf("parsevar\n");
    };
    if(!symTableInit)
    {
        initsyms();
        symTableInit = 1;
    }
    TOKEN symbol = talloc();
    TOKEN type = talloc();
    symbol = gettok();
    type = peektok();
    if((type->whichval + DELIMITER_BIAS) == COMMA)
    {
        type = gettok();
        type = parsevar(type);
    }
    else if((type->whichval + DELIMITER_BIAS) == COLON)
    {
        gettok();
        type = gettok();
        if(type->tokentype == RESERVED && type->whichval + RESERVED_BIAS == ARRAY)
        {
            SYMBOL arr = symalloc();
            arr->kind = ARRAYSYM;
            arr->datatype = NULL;
            TOKEN integer = talloc();
            gettok();
            integer = gettok();
            arr->lowbound = integer->intval;
            gettok();
            integer = gettok();
            arr->highbound = integer->intval;
            integer = gettok();
            if(integer->tokentype == DELIMITER && integer->whichval + DELIMITER_BIAS == COMMA)
            {
                integer = gettok();
                gettok();
                SYMBOL secondarr = symalloc();
                secondarr->kind = ARRAYSYM;
                secondarr->datatype = searchst(integer->stringval)->datatype;
                secondarr->size = searchst(integer->stringval)->size;
                secondarr->lowbound = searchst(integer->stringval)->lowbound;
                secondarr->highbound = 2;
                arr->datatype = secondarr;
            }
            integer = gettok();
            if(integer->tokentype != RESERVED && integer->whichval + RESERVED_BIAS != OF)
                yyerror("Missing OF");
            else
            {
                integer = gettok();
                if(arr->datatype == NULL)
                    arr->datatype = searchst(integer->stringval);
                if(arr->datatype->size)
                    arr->size = searchst(integer->stringval)->size * (arr->highbound - arr->lowbound + 1) * (arr->datatype->highbound + 1);
                else
                    arr->size = searchst(integer->stringval)->size * (arr->highbound - arr->lowbound + 1);
            }
            type->symtype = arr;
        }
        else
            type->symtype = searchst(type->stringval);
    }
    instvars(symbol, type);
    return type;
}

TOKEN instfields(TOKEN args, TOKEN type)
{
    SYMBOL sym, typesym; int align;
    int pos = 0;
    TOKEN tokenarray[10];
    if (DEBUG)
    {
        printf("instfields\n");
        dbugprinttok(args);
        dbugprinttok(type);
    }
    while(args != NULL)
    {
        sym = makesym(copytok(args)->stringval);
        args->symtype = searchins(copytok(type)->stringval);
        tokenarray[pos] = copytok(args);
        sym->size = args->symtype->size;
        args = copytok(args)->link;
        type = copytok(type)->link;
        pos = pos + 1;
    }
    pos = pos - 1;
    while(pos >= 0)
    {
        if(args == NULL)
            args = copytok(tokenarray[pos]);
        else
        {
            type = copytok(args);
            args = copytok(tokenarray[pos]);
            args->link = copytok(type);
        }
        pos = pos - 1;
    }
    if (DEBUG)
    {
        printf("instfields2\n");
        dbugprinttok(args);
        dbprsymbol(args->symtype);
    }
    return args;
}

SYMBOL copysym(SYMBOL origsym)
{
    SYMBOL newsym = symalloc();
    SYMBOL holder = symalloc();
    newsym->kind = origsym->kind;
    int i;
    for(i = 0; i < 16; i++)
    {
        newsym->namestring[i] = origsym->namestring[i];
    }
    newsym->basicdt = origsym->basicdt;
    newsym->datatype = origsym->datatype;
    newsym->blocklevel = origsym->blocklevel;
    newsym->size = origsym->size;
    newsym->offset = origsym->offset;
    newsym->link = origsym->link;
    newsym->datatype->link = origsym->datatype->link;
    return newsym;
}

/* instrec will install a record definition.  Each token in the linked list
   argstok has a pointer its type. */
TOKEN instrec(TOKEN rectok, TOKEN argstok)
{
    SYMBOL record = symalloc();
    SYMBOL typesym = symalloc();
    SYMBOL datatypes = symalloc();
    SYMBOL current = symalloc();
    datatypes = NULL;
    TOKEN holder = talloc();
    holder = copytok(argstok);
    int pos = 0;
    SYMBOL symbolarray[10];
    int align = 0;
    if (DEBUG)
    {
        printf("instrec\n");
        dbugprinttok(rectok);
        dbugprinttok(argstok);
    }
    while(argstok != NULL) /* for each argument */
    {
        current = searchins(argstok->stringval);
        current->datatype = argstok->symtype;
        typesym = argstok->symtype;
        if(align % 8 != 0 && alignsize(typesym) != 4)
            align = align + 4;
        current->offset = align;
        symbolarray[pos] = copysym(current);
        align = align + typesym->size;
        argstok = argstok->link;
        pos = pos + 1;
    }
    pos = pos - 1;
    if(searchst(rectok->stringval) == NULL)
        record = searchins(rectok->stringval);
    else
        record = searchst(rectok->stringval);
    int sizes = 0;
    while(pos >= 0)
    {
        record->link = searchins(holder->stringval);
       /* if(symbolarray[pos]->kind == POINTERSYM)
        {
            symbolarray[pos]->datatype = searchst(symbolarray[pos]->datatype->namestring);
        }*/
        if(datatypes == NULL && pos == 0)
        {
            datatypes = copysym(symbolarray[pos]);
            datatypes->kind = RECORDSYM;
            datatypes->datatype = copysym(symbolarray[pos]);
            datatypes->datatype->link = NULL;
            sizes = datatypes->datatype->size + sizes;
        }
        else if(datatypes == NULL)
        {
            datatypes = copysym(symbolarray[pos]);
            datatypes->datatype = copysym(symbolarray[pos]);
            datatypes->datatype->link = NULL;
            sizes = datatypes->datatype->size + sizes;
        }
        else if(pos > 0)
        {
            current = copysym(datatypes);
            datatypes = copysym(symbolarray[pos]);
            datatypes->datatype = copysym(symbolarray[pos]);
            datatypes->link = copysym(current);
            sizes = datatypes->datatype->size + sizes;
        }
        else
        {
            current = copysym(datatypes);
            datatypes = copysym(symbolarray[pos]);
            datatypes->datatype = copysym(symbolarray[pos]);
            datatypes->kind = RECORDSYM;
            datatypes->datatype->link = copysym(current);
            sizes = datatypes->datatype->size + sizes;
        }
        pos = pos - 1;
    }
    record->kind = TYPESYM;
    record->size = align;
    record->datatype = datatypes;
    if (DEBUG) printst();
    if (DEBUG)
    {
        printf("instrec\n");
        dbprsymbol(record);
        dbprsymbol(typesym);
        dbprsymbol(searchst(holder->stringval));
        dbugprinttok(holder);
    }
    return rectok;
}

/* Parse a TYPE statement add to the symbol table */
TOKEN parsetype(TOKEN keytok)
{
    if(DEBUG & DB_MAKEPROGN)
    {
        printf("parsetype\n");
    };
    if(!symTableInit)
    {
        initsyms();
        symTableInit = 1;
    }
    int pos = 0;
    int repeat = 0;
    TOKEN name = talloc();
    TOKEN args = talloc();
    TOKEN holder = talloc();
    TOKEN type = talloc();
    TOKEN argstok = talloc();
    TOKEN tokenarray[10];
    TOKEN typearray[10];
    name = gettok();
    gettok();
    if(peektok()->tokentype == RESERVED && peektok()->whichval + RESERVED_BIAS == RECORD)
    {
        while(!((holder->tokentype == RESERVED) && (holder->whichval+RESERVED_BIAS == END)))
        {
            keytok = gettok();
            args = gettok();
            holder = gettok();
            while((holder->whichval + DELIMITER_BIAS) != COLON)
            {
                args->link = gettok();
                holder = gettok();
                repeat = repeat + 1;
            }
            type = gettok();
            type->symtype = searchins(type->stringval);
            while(repeat > 0)
            {
                type = copytok(type);
                type->link = copytok(type);
                repeat = repeat - 1;
            }
            holder = peektok();
            tokenarray[pos] = copytok(args);
            typearray[pos] = copytok(type);
            pos = pos + 1;
        }
        args = NULL;
        type = NULL;
        pos = pos - 1;
        while(pos >= 0)
        {
            if(args == NULL)
                args = copytok(tokenarray[pos]);
            else
            {
                holder = copytok(args);
                args = copytok(tokenarray[pos]);
                args->link = copytok(holder);
            }
            if(type == NULL)
                type = copytok(typearray[pos]);
            else
            {
                holder = copytok(type);
                type = copytok(typearray[pos]);
                type->link = copytok(holder);
            }
            pos = pos - 1;
        }
        holder = gettok();
        if((holder->tokentype == RESERVED) && (holder->whichval+RESERVED_BIAS == END))
        {
            argstok = instfields(args, type);
            instrec(name, argstok);
        }
        else
            yyerror("Missing END");
    }
    else if(peektok()->tokentype == DELIMITER && peektok()->whichval + DELIMITER_BIAS == LPAREN)
    {
        holder = gettok();
        int i = 0;
        while(holder->whichval + DELIMITER_BIAS != RPAREN)
        {
            holder = gettok();
            type->tokentype = NUMBERTOK;
            type->datatype = INTEGER;
            type->intval = i;
            instconst(copytok(holder),copytok(type));
            holder = gettok();
            i = i + 1;
        }
        name = makesubrange(copytok(name), 0, i-1);
    }
    else if(peektok()->tokentype == OPERATOR && peektok()->whichval == POINTEROP)
    {
        gettok();
        SYMBOL pointer = symalloc();
        SYMBOL type = symalloc();
        type = searchins(name->stringval);
        type->kind = TYPESYM;
        type->datatype = pointer;
        type->size = 8;
        holder = gettok();
        pointer->kind = POINTERSYM;
        pointer->datatype = searchins(holder->stringval);
        pointer->size = basicsizes[POINTER];
    }
    return name;
}

/* makesubrange makes a SUBRANGE symbol table entry, puts the pointer to it
   into tok, and returns tok. */
TOKEN makesubrange(TOKEN tok, int low, int high)
{
    SYMBOL subrange = symalloc();
    SYMBOL type = symalloc();
    subrange->kind = SUBRANGE;
    subrange->basicdt = INTEGER;
    subrange->lowbound = low;
    subrange->highbound = high;
    subrange->size = basicsizes[INTEGER];
    type = insertsym(tok->stringval);
    type->kind = TYPESYM;
    type->size = 4;
    type->datatype = subrange;
    tok->symtype = type;
    return tok;
}

/* Parse a LABEL statement */
void parselabel(TOKEN keytok)
{
    if(DEBUG & DB_MAKEPROGN)
    {
        printf("parselabel\n");
    };
    keytok = peektok();
    while(keytok->whichval + DELIMITER_BIAS != SEMICOLON)
    {
        labelnames[labelpos] = gettok();
        labelpos = labelpos + 1;
        keytok = gettok();
    }
}

/* Parse a GOTO statement */
TOKEN parsegoto(TOKEN keytok)
{
    if(DEBUG & DB_MAKEPROGN)
    {
        printf("parsegoto\n");
    };
    keytok = gettok();
    int i;
    for(i = 0; i < labelpos; i++)
    {
        if(labelnames[i]->intval == keytok->intval)
        {
            keytok = makegoto(labeltokens[i]->operands->intval);
            break;
        }
    }
    return keytok;
}

/* Parse a Const statement, and add it to the symbol table */
TOKEN parseconst(TOKEN keytok)
{
    if(!symTableInit)
    {
        initsyms();
        symTableInit = 1;
    }
    TOKEN symbol = talloc();
    TOKEN type = talloc();
    symbol = gettok();
    type = peektok();
    if((type->tokentype == OPERATOR) && (type->whichval == EQOP))
    {
        gettok();
        type = gettok();
        instconst(symbol, type);
    }
    else
        yyerror("Missing ASSIGNMENT");
    return keytok;
}

TOKEN parseif(TOKEN keytok)  /* Parse an IF ... THEN ... ELSE statement */
{
    TOKEN expr, thenpart, elsepart, tok;
    TOKEN parseexpr();
    TOKEN statement();
    expr = parseexpr();
    tok = gettok();
    if (reserved(tok, THEN) == 0)
        yyerror("Missing THEN");
    thenpart = statement();
    elsepart = NULL;
    tok = peektok();
    if(reserved(tok, ELSE))
    {
        tok = gettok();        /* consume the ELSE */
        elsepart = statement();
    };
    return (makeif(keytok, expr, thenpart, elsepart));
}

/* Added coded to check the types of the assignee and the operands */
TOKEN parseassign(TOKEN lhs)  /* Parse an assignment statement */
{
    int pointer = 0;
    TOKEN pointertok = talloc();
    SYMBOL sym;
    TOKEN tok, rhs;
    TOKEN holder, holder2, holder3, fix;
    TOKEN parseexpr();
    holder = talloc();
    holder2 = talloc();
    holder3 = talloc();
    int state = 0;
    fix = talloc();
    tok = gettok();
    if(tok->tokentype == OPERATOR && tok->whichval == POINTEROP)
    {
        int size;
        gettok();
        pointertok = gettok();
        sym = searchst(pointertok->stringval);
        size = sym->offset;
        holder->datatype = OPERATOR;
        holder->whichval = AREFOP;
        if(peektok()->tokentype == OPERATOR && peektok()->whichval == POINTEROP)
        {
            lhs = binop(holder, unaryop(copytok(tok),  copytok(lhs)), getnumbertok(size));
            while(peektok()->tokentype == OPERATOR && peektok()->whichval == POINTEROP)
            {
                gettok();
                gettok();
                holder3 = gettok();
                sym = searchst(holder3->stringval);
                size = sym->offset;
                if(peektok()->tokentype == OPERATOR && peektok()->whichval == DOTOP)
                {
                    gettok();
                    holder2 = gettok();
                    sym = searchst(holder2->stringval);
                    size = size + sym->offset;
                }
                lhs = binop(holder, unaryop(copytok(tok),  copytok(lhs)), getnumbertok(size));
            }
        }
        else
        {
            if(peektok()->tokentype == OPERATOR && peektok()->whichval == DOTOP)
            {
                gettok();
                holder2 = gettok();
                sym = searchst(holder2->stringval);
                size = size + sym->offset;
            }
            lhs = binop(holder, unaryop(copytok(tok),  copytok(lhs)), getnumbertok(size));
        }
        tok = gettok();
    }
    else if(tok->tokentype == DELIMITER && tok->whichval + DELIMITER_BIAS == LBRACKET)
    {
        int sizearray;
        int secondarray;
        tok = gettok(); //7
        SYMBOL arraysym = symalloc();
        arraysym = searchst(lhs->stringval); //lhs = ac
        sizearray = arraysym->datatype->datatype->size;
        if(arraysym->datatype->datatype->kind == ARRAYSYM)
        {
            sizearray = sizearray * (arraysym->datatype->datatype->highbound - arraysym->datatype->datatype->lowbound + 1);
        }
        gettok();
        if(peektok()->tokentype == OPERATOR && peektok()->whichval == DOTOP)
        {
            gettok();
            holder3 = NULL;
        }
        else
        {
            holder3 = gettok();
        }
        if(tok->tokentype == NUMBERTOK)
        {
            tok->intval = tok->intval - 1;
            sizearray = tok->intval * sizearray;
            holder = gettok(); //re
            holder2->tokentype = OPERATOR;
            holder2->whichval = AREFOP;
            lhs = binop(copytok(holder2), copytok(lhs), getnumbertok(sizearray));
        }
        else
        {
            secondarray = 0;
            if(holder3 != NULL)
            {
                 holder3 = lookup(copytok(holder3));
            }
            holder = gettok(); //i
            holder2->tokentype = OPERATOR;
            holder2->whichval = TIMESOP;
            tok = binop(copytok(holder2), getnumbertok(sizearray), copytok(tok));
            holder2->whichval = PLUSOP;
            if(holder3 != NULL)
                tok = binop(copytok(holder2), getnumbertok((sizearray*-1) + (holder3->intval*arraysym->datatype->datatype->size)), copytok(tok));
            else
                tok = binop(copytok(holder2), getnumbertok((sizearray*-1)), copytok(tok));
            holder2->whichval = AREFOP;
            lhs = binop(copytok(holder2), copytok(lhs), copytok(tok));
        }
        tok = gettok();
    }
    if (tok->tokentype != OPERATOR || tok->whichval != ASSIGNOP )
        printf("Unrecognized statement\n");
    sym = searchst(lhs->stringval);
    rhs = parseexpr();
    if(sym != NULL && sym->datatype->basicdt == INTEGER)
    {
        if(real)
        {
            holder = copytok(rhs->operands);
            sym = searchst(holder->stringval);
            if(sym != NULL && sym->datatype->basicdt == INTEGER && holder->tokentype != 0)
            {
                holder2->tokentype = OPERATOR;
                holder2->whichval = FLOATOP;
                unaryop(holder2, holder);
                holder2->link = rhs->operands->link;
                rhs->operands = copytok(holder2);
            }
            else if(holder->tokentype == NUMBERTOK && holder->datatype == INTEGER)
            {
                holder2 = rhs->operands->link;
                rhs->operands->datatype = REAL;
                rhs->operands->realval = holder->intval*1.0;
                rhs->operands->link = copytok(holder2);
            }
            holder = copytok(rhs->operands->link);
            sym = searchst(holder->stringval);
            if(sym != NULL && sym->datatype->basicdt == INTEGER && holder->tokentype != 0)
            {
                holder2->tokentype = OPERATOR;
                holder2->whichval = FLOATOP;
                unaryop(holder2, holder);
                rhs->operands->link = copytok(holder2);
            }
            else if(holder->tokentype == NUMBERTOK && holder->datatype == INTEGER)
            {
                rhs->operands->link->realval = holder->intval*1.0;
                rhs->operands->link->datatype = REAL;
            }
            state = 1;
            fix->tokentype = OPERATOR;
            fix->whichval = FIXOP;
            unaryop(fix, rhs);
            rhs = copytok(unaryop(fix, rhs));
        }
        real = 0;
    }
    else if(sym != NULL && sym->datatype->basicdt == REAL)
    {
        holder = copytok(rhs->operands);
        sym = searchst(holder->stringval);
        if(sym != NULL && sym->datatype->basicdt == INTEGER && holder->tokentype != 0)
        {
            holder2->tokentype = OPERATOR;
            holder2->whichval = FLOATOP;
            unaryop(holder2, holder);
            holder2->link = rhs->operands->link;
            rhs->operands = copytok(holder2);
        }
        else if(holder->tokentype == NUMBERTOK && holder->datatype == INTEGER)
        {
            holder2 = rhs->operands->link;
            rhs->operands->datatype = REAL;
            rhs->operands->realval = holder->intval*1.0;
            rhs->operands->link = copytok(holder2);
        }
        holder = copytok(rhs->operands->link);
        sym = searchst(holder->stringval);
        if(sym != NULL && sym->datatype->basicdt == INTEGER && holder->tokentype != 0)
        {
            holder2->tokentype = OPERATOR;
            holder2->whichval = FLOATOP;
            unaryop(holder2, holder);
            rhs->operands->link = copytok(holder2);
        }
        else if(holder->tokentype == NUMBERTOK && holder->datatype == INTEGER)
        {
            rhs->operands->link->realval = holder->intval*1.0;
            rhs->operands->link->datatype = REAL;
        }
    }
    return (binop(tok, lhs, rhs));
}

/* *opstack and *opndstack allow reduce to manipulate the stacks of parseexpr */
void reduce(TOKEN *opstack, TOKEN *opndstack)  /* Reduce an op and 2 operands */
{
    TOKEN op, lhs, rhs;
    if (DEBUG & DB_EXPR)
    {
        printf("reduce\n");
    };
    op = *opstack;               /* pop one operator from op stack */
    *opstack = op->link;
    rhs = *opndstack;            /* pop two operands from opnd stack */
    lhs = rhs->link;
    *opndstack = lhs->link;
    *opndstack = cons(binop(op,lhs,rhs), *opndstack);  /* push result opnd */
}

/* *opstack and *opndstack allow reduce to manipulate the stacks of parseexpr */
void reduce2(TOKEN *opstack, TOKEN *opndstack)  /* Reduce an op and an operand */
{
    TOKEN op, lhs;
    if (DEBUG & DB_EXPR)
    {
        printf("reduce\n");
    };
    op = *opstack;               /* pop one operator from op stack */
    *opstack = op->link;
    lhs = *opndstack;            /* pop one operand from opnd stack */
    *opndstack = lhs->link;
    *opndstack = cons(unaryop(op,lhs), *opndstack);  /* push result opnd */
}

/*                             +     *                                     */
static int precedence[] = { 0, 1, 0, 3    };  /* **** trivial version **** */

TOKEN parseexpr()   /* Parse an expression using operator precedence */
{                   /* Partial implementation -- handles +, *, ()    */
    TOKEN tok, op, lhs, rhs, sym;
    int state, done;
    TOKEN opstack, opndstack;
    if (DEBUG & DB_EXPR)
    {
        printf("parseexpr\n");
    };
    done = 0;
    state = 0;
    opstack = NULL;
    opndstack = NULL;
    while (done == 0)
    {
        tok = peektok();
        switch(tok->tokentype)
        {
            case IDENTIFIERTOK:
                tok = gettok();
                sym = lookup(tok);
                if(sym != NULL)
                    tok = sym;
                if(peektok()->tokentype == OPERATOR && peektok()->whichval == POINTEROP)
                {
                    TOKEN pointer = talloc();
                    TOKEN offset = talloc();
                    TOKEN areftok = talloc();
                    int offsize;
                    pointer = gettok();
                    areftok->tokentype = OPERATOR;
                    areftok->whichval = AREFOP;
                    gettok();
                    offset = gettok();
                    offsize = searchst(offset->stringval)->offset;
                    if(peektok()->tokentype == OPERATOR && peektok()->whichval == DOTOP)
                    {
                        gettok();
                        offset = gettok();
                        dbprsymbol(searchst(offset->stringval));
                        offsize = offsize + searchst(offset->stringval)->offset;
                    }
                    tok = binop(areftok, unaryop(pointer, copytok(tok)), getnumbertok(offsize));
                    opndstack = cons(tok, opndstack);
                }
                else if(peektok()->tokentype == DELIMITER && (peektok()->whichval + DELIMITER_BIAS) == LPAREN)
                    opndstack = cons(parsefuncall(tok), opndstack);
                else
                    opndstack = cons(tok, opndstack);
                break;
            case NUMBERTOK: /* operand: push onto stack */
                tok = gettok();
                opndstack = cons(tok, opndstack);
                break;
            case DELIMITER:
                if((tok->whichval + DELIMITER_BIAS) == LPAREN)
                {
                    tok = gettok();
                    opstack = cons(tok, opstack);
                    if(peektok()->whichval == MINUSOP)
                        bin = 0;
                }
                else if((tok->whichval + DELIMITER_BIAS) == RPAREN)
                {
                    tok = gettok();
                    done = 1;
                    while(opstack != NULL && (opstack->whichval + DELIMITER_BIAS) != LPAREN)
                    {
                        if(bin)
                            reduce(&opstack, &opndstack);
                        else
                            reduce2(&opstack, &opndstack);
                        bin = 1;
                    }
                    opstack = opstack->link; /* discard the left paren */
                }
                else if((tok->whichval + DELIMITER_BIAS) == COMMA)
                {
                    tok = gettok();
                }
                else done = 1;
                break;
            case OPERATOR:
                if(tok->whichval != DOTOP) /* special case for now */
                {
                    tok = gettok();
                    while(opstack != NULL && opstack->tokentype != DELIMITER && (precedence[opstack->whichval] >= precedence[tok->whichval]))
                        reduce(&opstack, &opndstack);
                    opstack = cons(tok, opstack);
                }
                else done = 1;
                break;
            case STRINGTOK:
                tok = gettok();
                opndstack = cons(tok, opndstack);
                break;
            case RESERVED:
                if(tok->whichval + RESERVED_BIAS == NIL)
                {
                    tok = gettok();
                    tok->tokentype = NUMBERTOK;
                    tok->datatype = POINTER;
                    tok->intval = 0;
                    opndstack = cons(tok, opndstack);
                }
                else
                    done = 1;
                break;
            default: done = 1;
        }
    }
    while (opstack != NULL) reduce(&opstack, &opndstack);
    return (opndstack);
}

TOKEN statement()    /* Parse a Pascal statement: the "big switch" */
{
    SYMBOL sym = symalloc();
    TOKEN tok, result, symbol;
    result = NULL;
    tok = gettok();
    if (tok->tokentype == RESERVED)
    {
        switch (tok->whichval + RESERVED_BIAS)   /* the big switch */
        {
            case BEGINBEGIN:
                result = parsebegin(tok);
                break;
            case IF:
                result = parseif(tok);
                break;
            case PROGRAM:
                result = parseprogram(tok);
                break;
            case FOR:
                result = parsefor(tok);
                break;
            case REPEAT:
                result = parserepeat(tok);
                break;
            case WHILE:
                result = parsewhile(tok);
                break;
            case CONST:
                while(multvar)
                {
                    parseconst(tok);
                    gettok();
                    result = peektok();
                    if(result->tokentype == RESERVED)
                        multvar = 0;
                }
                multvar = 1;
                result = statement();
                break;
            case VAR:
                blockoffs[blocknumber] = 0;
                while(multvar)
                {
                    parsevar(tok);
                    gettok();
                    result = peektok();
                    if(result->tokentype == RESERVED)
                        multvar = 0;
                }
                multvar = 1;
                result = statement(); 
                break;
            case TYPE:
                while(multvar)
                {
                    parsetype(tok);
                    gettok();
                    result = peektok();
                    if(result->tokentype == RESERVED)
                        multvar = 0;
                }
                multvar = 1;
                result = statement(); 
                break;
            case LABEL:
                parselabel(tok);
                result = statement();
                break;
            case GOTO:
                result = parsegoto(tok);
                break;
        }
    }
    else if (tok->tokentype == IDENTIFIERTOK)
    {
        symbol = lookup(tok);
        if(symbol != NULL)
            tok = symbol;
        if(peektok()->tokentype==DELIMITER && peektok()->whichval+DELIMITER_BIAS==LPAREN)
            result = parsefuncall(tok);
        else
            result = parseassign(tok);
    }
    else if (tok->tokentype == NUMBERTOK)
    {
        gettok();
        int i;
        for(i = 0; i < labelpos; i++)
        {
            if(labelnames[i]->intval == tok->intval)
            {
                TOKEN labeltok = talloc();
                labeltok = makelabel();
                labeltokens[i] = copytok(labeltok);
                result = statement();
                labeltok->link = result;
                result = makeprogn(talloc(), labeltok);
                break;
            }
        }
    }
    return (result);
}

int yyparse()             /* program = statement . */
{
    TOKEN dottok;
    savedtoken = NULL;
    parseresult = statement();    /* get the statement         */
    dottok = gettok();            /* get the period at the end */
    if (dottok->tokentype == OPERATOR && dottok->whichval == DOTOP)
        return (0);
    else return(1);
}


main()          /* Call yyparse repeatedly to test */
{ 
    int res;
    initscanner();
    init_charclass();   /* initialize character class array */
    //printf("Started parser test.\n");
    res = yyparse();
    //printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES)
        dbugprinttok(parseresult);
    else
        //printst();
    //ppexpr(parseresult);
    gencode(parseresult, blockoffs[blocknumber], labelnum);
}
