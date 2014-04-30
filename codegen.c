/* codgen.c       Generate Assembly Code for x86         15 May 13   */

/* Copyright (c) 2013 Gordon S. Novak Jr. and The University of Texas at Austin
    */

/* Starter file for CS 375 Code Generation assignment.           */
/* Written by Gordon S. Novak Jr.                  */

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

#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "symtab.h"
#include "genasm.h"
#include "codegen.h"

void genc(TOKEN code);

/* Set DEBUGGEN to 1 for debug printouts of code generation */
#define DEBUGGEN 0

int nextlabel;    /* Next available label number */
int stkframesize;   /* total stack frame size */
int currentreg;
int currentfloatreg = 8;

/* Top-level entry for code generator.
   pcode    = pointer to code:  (program foo (output) (progn ...))
   varsize  = size of local storage in bytes
   maxlabel = maximum label number used so far

Add this line to the end of your main program:
    gencode(parseresult, blockoffs[blocknumber], labelnumber);
The generated code is printed out; use a text editor to extract it for
your .s file.
         */

void gencode(TOKEN pcode, int varsize, int maxlabel)
{
    TOKEN name, code;
    name = pcode->operands;
    code = name->link->link;
    nextlabel = maxlabel + 1;
    stkframesize = asmentry(name->stringval,varsize);
    genc(code);
    asmexit(name->stringval);
}

/* Trivial version: always returns RBASE + 0 */
/* Get a register.   */
/* Need a type parameter or two versions for INTEGER or REAL */
int getreg(int kind)
{
    /*     ***** fix this *****   */
    return RBASE;
}

/* Trivial version */
/* Generate code for arithmetic expression, return a register number */
int genarith(TOKEN code)
{
    int num, reg, offs;
    SYMBOL sym;
    if(DEBUGGEN)
    {
        printf("genarith\n");
	    dbugprinttok(code);
    };
    switch(code->tokentype)
    {
        case NUMBERTOK:
            switch(code->datatype)
            {
                case INTEGER:
                    num = code->intval;
                    reg = currentreg;
                    if(num >= MINIMMEDIATE && num <= MAXIMMEDIATE)
                        asmimmed(MOVL, num, reg);
                    break;
                case REAL:
                    /*     ***** fix this *****    */
                    makeflit(code->realval, nextlabel);
                    nextlabel =  nextlabel + 1;
                    reg = currentfloatreg;
                    currentfloatreg = currentfloatreg + 1;
                    if(code->realval >= MINIMMEDIATE && code->realval <= MAXIMMEDIATE)
                    {
                        asmldflit(MOVSD, nextlabel-1, reg);
                    }
                    break;
           }
           break;
        case IDENTIFIERTOK:
            /*     ***** fix this *****   */
            reg = currentreg;
            sym = code->symentry;
            offs = sym->offset - stkframesize;
                asmld(MOVL, offs, reg, code->stringval);
            break;
        case OPERATOR:
            /*     ***** fix this *****   */
            //genarith(code->operands->operands);
            //reg = getreg(WORD);
            if(code->whichval == FLOATOP)
            {
                currentreg = 0;
                reg = genarith(code->operands);
                asmfloat(reg, currentfloatreg);
                reg = currentfloatreg;
                currentfloatreg = currentfloatreg + 1;
            }
            else
            {
                currentreg = 0;
                reg = genarith(code->operands);
                currentreg = currentreg + 1;
                if(code->whichval == MINUSOP && code->operands->link == NULL)
                {
                    asmfneg(reg, currentreg);
                    reg = currentreg;
                    break;
                }
                else
                    num = genarith(code->operands->link);
                switch(code->whichval)
                {
                    case EQOP:
                    case NEOP:
                    case LTOP:
                    case LEOP:
                    case GEOP:
                    case GTOP:
                        asmrr(CMPL, num, reg);
                        break;
                    case PLUSOP:
                        asmrr(ADDL, num, reg);
                        break;
                    case TIMESOP:
                        asmrr(MULSD, num, reg);
                        break;
                }
            }
            break;
    };
    return reg;
}


/* Generate code for a Statement from an intermediate-code form */
void genc(TOKEN code)
{
    TOKEN tok, lhs, rhs;
    int reg, offs, endlabel;
    SYMBOL sym;
    if(DEBUGGEN)
    {
        printf("genc\n");
        dbugprinttok(code);
    };
    if(code->tokentype != OPERATOR)
    {
        printf("Bad code token");
        dbugprinttok(code);
    };
    switch(code->whichval)
    {
        case PROGNOP:
            tok = code->operands;
            while(tok != NULL)
            {
                genc(tok);
                tok = tok->link;
            };
            break;
        case ASSIGNOP:                   /* Trivial version: handles I := e */
            lhs = code->operands;
            rhs = lhs->link;
            reg = genarith(rhs);              /* generate rhs into a register */
            sym = lhs->symentry;              /* assumes lhs is a simple var  */
            offs = sym->offset - stkframesize; /* net offset of the var   */
            switch(lhs->datatype)            /* store value into lhs  */
            {
                case INTEGER:
                    asmst(MOVL, reg, offs, lhs->stringval);
                    break;
                case REAL:
                    asmst(MOVSD, reg, offs, lhs->stringval);
                    break;
                    /* ...  */
            };
            break;
        case LABELOP:
            asmlabel(code->operands->intval);
            break;
        case GOTOOP:
            asmjump(JMP, code->operands->intval);
            break;
        case FUNCALLOP:
            makeblit(code->operands->link->stringval, nextlabel);
            nextlabel =  nextlabel + 1;
            reg = currentreg;
            asmlitarg(nextlabel-1, EDI);
            asmcall(code->operands->stringval);
            break;
        case IFOP:
            //lhs = code->operands;      // <=
            //rhs = lhs->operands;       // i
            //rhs = lhs->operands->link; // lim
            genarith(code->operands);
            switch(code->operands->whichval)
            {
                case NEOP:
                    asmjump(JNE, nextlabel++);
                case EQOP:
                    asmjump(JE, nextlabel++);
                case GEOP:
                    asmjump(JGE, nextlabel++);
                case LTOP:
                    asmjump(JL, nextlabel++);
                case GTOP:
                    asmjump(JG, nextlabel++);
                case LEOP:
                    asmjump(JLE, nextlabel++);
            }
            endlabel = nextlabel;
            asmjump(JMP, nextlabel++);
            asmlabel(nextlabel - 2);
            genc(code->operands->link);
            asmlabel(endlabel);
            break;
    };
}
