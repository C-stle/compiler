#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>

#define MaxSymbols 200
#define MaxRules 100
#define MaxNumberOfStates 200

#define EOF_TOK 48

typedef struct ssym {
	int kind;
	int no;
	char str[10];
} sym;

typedef struct orule {
	sym leftside;
	sym rightside[10];
	int rleng;
} onerule;

//typedef struct twoints {
//	int cr;
//	int elm;
//} element_stack;

typedef struct tkt {
	int kind;
	char sub_kind[3];
	int sub_data;
	double rnum;
	char str[20];
} tokentype;

typedef char oneword[50];

char keywords[17][50] =
{ "if", "else","while","do","for","include","define","typedef","struct","int","char","float", "double","void","return","case","then" };
int total_keywords = 17;
int idx_First_keyword = 31;

typedef struct symtbl { oneword idstr; int attribute; } sym_ent;
sym_ent symtbl[500];
int total_ids = 0;

typedef struct typeitemnode *ty_ptr_item_node;
typedef struct typeitemnode {
	int RuleNum;
	int DotNum;
	ty_ptr_item_node link;
} type_item;

typedef struct statenode* state_node_ptr;
typedef struct statenode {
	int id;
	int item_cnt;
	ty_ptr_item_node item_start;
	state_node_ptr next;
} state_node;

typedef struct itemnode* Arc_node_ptr;
typedef struct itemnode {
	int from_state;
	int to_state;
	sym gram_sym; 
	Arc_node_ptr link;
} Arc_node;

typedef struct gotoset* goto_set_ptr;
typedef struct gotoset {
	Arc_node_ptr Arc_list;
	state_node_ptr State_Node_List;
} goto_set;

typedef struct cell_action_tbl {
	char Kind;
	int num;
} ty_Cell_Action_Table;

typedef struct nodetype *Ty_Node_Ptr;
typedef struct nodetype {
	int state;
	sym nodesym;
	int child_cnt;
	Ty_Node_Ptr children[10];
	int rule_no_used;
} nodeT;

state_node_ptr Add_A_State_Node(state_node_ptr State_Node_List_Header, ty_ptr_item_node To_List);
void Add_An_Arc(Arc_node_ptr *Arc_List_Header, int from_num, int to_num, sym Symbol);
int CheckExistItem(ty_ptr_item_node cs_list, ty_ptr_item_node s_val);
void Clear_Action_Table(void);
void Clear_Goto_Table(void);
ty_ptr_item_node closure(ty_ptr_item_node IS);
int Compute_first_of_one_nonterminal(sym X);
int Compute_first_of_any_string(sym alpha[], int first_result[]);
int Compute_follow_of_one_nonterminal(int idx_NT);
int deleteTyPtrItemNode(ty_ptr_item_node item_list);
int findToStateNodeId(Arc_node_ptr arc_list, int from_id, sym symbol);
void fitemListPrint(ty_ptr_item_node IS, FILE *fpw);
ty_ptr_item_node getLastItem(ty_ptr_item_node cs_list);
sym get_next_token(FILE *fps);
ty_ptr_item_node GoTo(ty_ptr_item_node IS, sym sym_val);
void printGotoGraph(goto_set_ptr gsp);
void ItemListPrint(ty_ptr_item_node IS);
tokentype lexan(FILE *fps);
int lookUp_nonterminal(char *str);
int lookUp_terminal(char *str);
void Make_Action_Table();
void Make_Goto_Table();
Arc_node_ptr makeArcNode(void);
void makeGotoGraph(ty_ptr_item_node IS_0);
state_node_ptr makeStateNode(void);
Ty_Node_Ptr Parsing(FILE *fps);
void print_Action_Table(void);
void print_Goto_Table(void);
void print_parse_tree(FILE *fout, Ty_Node_Ptr curr, int standard, int first, int child);
void push_state(Ty_Node_Ptr Stack[], int State);
void push_symbol(Ty_Node_Ptr Stack[], Ty_Node_Ptr NodeToPush);
Ty_Node_Ptr pop();
void read_grammer(char *fileName);
int is_same_two_itemlists(ty_ptr_item_node list1, ty_ptr_item_node list2);
int itemListCounter(ty_ptr_item_node IS);

int MaxTerminal;
int MaxNonterminal;
sym Nonterminals_list[MaxSymbols];
sym Terminals_list[MaxSymbols];

int totalNumberOfRules;
onerule rules[MaxRules];

int FirstTable[MaxSymbols][MaxSymbols];
int FollowTable[MaxSymbols][MaxSymbols];
goto_set_ptr States_And_Arcs = NULL;
int Number_Of_States = 0;
int NumberOfArcs = 0;
ty_Cell_Action_Table Action_Table[MaxNumberOfStates][MaxSymbols];
int Goto_Table[MaxNumberOfStates][MaxSymbols];
Ty_Node_Ptr Stack[1000];
int Top = -1;

Ty_Node_Ptr Root = NULL;
int bar[100];

FILE *fps;

tokentype lexan() {
	int state = 0;
	char c;
	char buf[50];
	int bp = 0; // bp is buffer pointer(다음 넣을 위치).
	int upper_n; // number 토큰에서 소숫점 위 부분 즉 정수 부분을 저장함.
	double fraction; // number 토큰에서 소숫점 아래 부분을 저장함.
	tokentype token;
	int idx, FCNT, sign, Enum;

	while (1) {
		switch (state) {
		case 0: // 초기 상태. 각 토큰의 첫 글자에 따라서 작업 수행 및 다음 상태 결정함.
			c = fgetc(fps);  // fgetc can be called even if fp is after the end of file.
							// calling it again still returns EOF(-1) w/o invoking error.
			if (iswhitespace(c)) state = 0;  // this is white space.
			else if (isalpha(c)) { buf[bp] = c; bp++; buf[bp] = '\0'; state = 28; }
			else if (isdigit(c)) { buf[bp] = c; bp++; buf[bp] = '\0'; upper_n = c - '0'; state = 1; }
			else if (c == '<') state = 2;
			else if (c == '>') state = 32;
			else if (c == '=') state = 35;
			else if (c == '!') state = 38;
			else if (c == '+') state = 3;
			else if (c == '-') state = 4;
			else if (c == '*') state = 52;
			else if (c == '/') state = 8;
			else if (c == '\\') state = 53;
			else if (c == '%') state = 54;
			else if (c == '.') state = 55;
			else if (c == ',') state = 56;
			else if (c == '(') state = 57;
			else if (c == ')') state = 58;
			else if (c == '{') state = 59;
			else if (c == '}') state = 60;
			else if (c == '[') state = 61;
			else if (c == ']') state = 62;
			else if (c == ':') state = 63;
			else if (c == ';') state = 64;
			else if (c == '"') state = 65;
			else if (c == '\'') state = 66;
			else if (c == '#') state = 67;
			else if (c == '|') state = 68;
			else if (c == '&') state = 5;
			else if (c == EOF) state = 71;
			else {
				token.kind = EOF_TOK; // 인식할 수 없는 토큰임을 나타냄.
				return token;
			}
			break;
		case 1: // NUM 토큰의 소수점 위 숫자열을 받아 들이는 상태.
			c = fgetc(fps);
			if (isdigit(c)) { buf[bp] = c; bp++; buf[bp] = '\0'; upper_n = 10 * upper_n + c - '0'; state = 1; }
			else if (c == '.') { buf[bp] = c; bp++; buf[bp] = '\0'; fraction = 0; FCNT = 0; state = 9; } // 소수점을 나왔으므로 실수를 처리하는 상태로 감.
			else if (c == 'E') { buf[bp] = c; bp++; buf[bp] = '\0'; fraction = 0; state = 16; }  // E 가 있는 exponent 처리부로 감.
			else state = 14;
			break;
		case 2: // 글자 < 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '=') state = 30;
			else state = 31;
			break;
		case 3: // 글자 + 가 나온 후의 처리를 담당하는 상태.
				//
			c = fgetc(fps);
			if (c == '=') state = 45;
			else if (c == '+') state = 47;
			else state = 46;
			break;
				//
		case 4: // 글자 - 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '-') state = 48;
			else if (c == '=') state = 49;
			else if (c == '>') state = 51;
			else state = 50;
			break;
		case 5: // 글자 + 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '&') state = 6;
			else state = 7;
			break;
		case 6:
			token.kind = 2; strcpy(token.sub_kind, "");		 strcpy(token.str, "&&");
			return token;
		case 7: // 토큰 & 를 리턴해주는 상태.
			ungetc(c, fps);
			token.kind = 13;
			return token;
		case 8:
			c = fgetc(fps);
			if (c == '/') state = 74;
			else if (c == '*') state = 75;
			else if (c == EOF) state = 73;
			else state = 72;
			break;
		case 9: // 실수의 소수점 이하를 받아 들이는 상태
			c = fgetc(fps);
			if (isdigit(c)) {
				buf[bp] = c; bp++; buf[bp] = '\0';
				FCNT++; fraction = fraction + (c - '0') / pow(10.0, FCNT); state = 23;
			}
			else if (c == 'E') { buf[bp] = c; bp++; buf[bp] = '\0'; state = 16; }
			else if (c == EOF)  state = 26;
			else if (iswhitespace(c)) state = 24;
			else state = 25;
			break;
		case 14: // 양의 정수 토큰을 리턴하는 상태.
			ungetc(c, fps);
			token.kind = 1; strcpy(token.sub_kind, "in"); // 양의 정수를 나타냄.
			token.sub_data = upper_n;
			strcpy(token.str, buf);
			return token;
		case 16:
			c = fgetc(fps);
			if (c == '+') { buf[bp] = c; bp++; buf[bp] = '\0'; sign = 1; state = 17; }
			else if (c == '-') { buf[bp] = c; bp++; buf[bp] = '\0'; sign = -1; state = 17; }
			else if (isdigit(c)) { buf[bp] = c; bp++; buf[bp] = '\0'; sign = 1; Enum = c - '0'; state = 18; }
			else  state = 25; // error! 		 
			break;
		case 17:
			c = fgetc(fps);
			if (isdigit(c)) { buf[bp] = c; bp++; buf[bp] = '\0'; Enum = c - '0'; state = 18; }
			else state = 25; // error!
			break;
		case 18:
			c = fgetc(fps);
			if (isdigit(c)) { buf[bp] = c; bp++;  buf[bp] = '\0'; Enum = Enum * 10 + c - '0'; state = 18; }
			else state = 19;
			break;
		case 19:
			ungetc(c, fps);
			token.kind = 1; strcpy(token.sub_kind, "do"); // 실수를 나타냄.
			token.rnum = (upper_n + fraction) * pow(10.0, sign*Enum);
			strcpy(token.str, buf);
			return token;

		case 20:
			strcpy(token.str, buf);
			idx = lookup_keyword_tbl(buf);
			if (idx >= 0) {
				token.kind = idx_First_keyword + idx;
				return token;
			}
			idx = lookup_symtbl(buf);
			if (idx >= 0) {
				token.kind = 0;
				token.sub_data = idx;
				return token;
			}
			strcpy(symtbl[total_ids].idstr, buf);
			total_ids++;
			token.kind = 0;
			token.sub_data = total_ids - 1;
			return token;

		case 23:
			c = fgetc(fps);
			if (isdigit(c)) {
				buf[bp] = c; bp++; buf[bp] = '\0';
				FCNT++; fraction = fraction + (c - '0') / pow(10.0, FCNT); state = 23;
			}
			else if (c == 'E') { buf[bp] = c; bp++; buf[bp] = '\0'; state = 16; }
			else state = 24;
			break;
		case 24:
			ungetc(c, fps);
			token.kind = 1; strcpy(token.sub_kind, "do"); // 실수를 나타냄.
			token.rnum = upper_n + fraction;
			strcpy(token.str, buf);
			return token;
		case 25:
			token.kind = -1;
			return token;
		case 26:  // do not call ungetc.
			token.kind = 1; strcpy(token.sub_kind, "do"); // 실수를 나타냄.
			token.rnum = upper_n + fraction;
			strcpy(token.str, buf);
			return token;
		case 28:
			c = fgetc(fps);
			if (isalpha(c) || isdigit(c) || c == '_') { buf[bp] = c; bp++; buf[bp] = '\0'; state = 28; }
			else	 state = 29;
			break;
		case 29: // id 나 keyword 
			ungetc(c, fps);
			strcpy(token.str, buf);
			idx = lookup_keyword_tbl(buf); // -1 if not exist.
			if (idx >= 0) { token.kind = 31 + idx; return token; }  // Note: first keyword has token index 30.
																	// reaches here if it is not a keyword.
			idx = lookup_symtbl(buf); // -1 if not exist.
			if (idx >= 0) { token.kind = 0; token.sub_data = idx; return token; }
			// reaches here if it is not in symbol table.
			strcpy(symtbl[total_ids].idstr, buf); total_ids++;
			token.kind = 0; // ID 토큰임을 나타냄.
			token.sub_data = total_ids - 1; // 이 ID 가 들어 있는 심볼테이블 엔트리 번호.
			return token;
		case 30:
			token.kind = 2; strcpy(token.sub_kind, "LE"); strcpy(token.str, "<=");
			return token;
		case 31:
			ungetc(c, fps);
			token.kind = 2; strcpy(token.sub_kind, "LT"); strcpy(token.str, "<");
			return token;
		case 32:
			c = fgetc(fps);
			if (c == '=') state = 33;
			else state = 34;
			break;
		case 33:
			token.kind = 2; strcpy(token.sub_kind, "GE");	strcpy(token.str, ">=");
			return token;
		case 34:
			ungetc(c, fps);
			token.kind = 2; strcpy(token.sub_kind, "GT"); strcpy(token.str, ">");
			return token;
		case 35: // 글자 = 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '=') state = 36;
			else state = 37;
			break;
		case 36: // 토큰 == 에 대한 처리를 수행하는 상태.
			token.kind = 2; strcpy(token.sub_kind, "EQ");	strcpy(token.str, "==");
			return token;
		case 37: // 토큰 > 에 대한 처리를 수행하는 상태.
			ungetc(c, fps);
			token.kind = 8; strcpy(token.str, "=");
			return token;
		case 38:
			c = fgetc(fps);
			if (c == '=') state = 39;
			else state = 40;
			break;
		case 39:
			token.kind = 2; strcpy(token.sub_kind, "NE");	 strcpy(token.str, "!=");
			return token;
		case 40:
			ungetc(c, fps);
			token.kind = 10;  strcpy(token.str, "!"); // NOT		
			return token;
		case 45:
			token.kind = 16; 		 strcpy(token.str, "+=");
			return token;
		case 46:
			ungetc(c, fps);
			token.kind = 3;  strcpy(token.str, "+");
			return token;
		case 47:
			token.kind = 14;		 strcpy(token.str, "++");
			return token;
		case 48:
			token.kind = 15;		 strcpy(token.str, "--");
			return token;
		case 49:
			ungetc(c, fps);
			token.kind = 17;  strcpy(token.str, "-=");
			return token;
		case 50:
			ungetc(c, fps);
			token.kind = 4;		 strcpy(token.str, "-");
			return token;
		case 51:
			token.kind = 9;		 strcpy(token.str, "->");
			return token;
		case 52:
			token.kind = 5;		 strcpy(token.str, "*");
			return token;
		case 53:
			token.kind = 30;		 strcpy(token.str, "\\");
			return token;
		case 54:
			token.kind = 7;		 strcpy(token.str, "%");
			return token;
		case 55:
			token.kind = 11;		 strcpy(token.str, ".");
			return token;
		case 56:
			token.kind = 12;		 strcpy(token.str, ",");
			return token;
		case 57:
			token.kind = 18;		 strcpy(token.str, "(");
			return token;
		case 58:
			token.kind = 19;		 strcpy(token.str, ")");
			return token;
		case 59:
			token.kind = 20;		 strcpy(token.str, "{");
			return token;
		case 60:
			token.kind = 21;		 strcpy(token.str, "}");
			return token;
		case 61:
			token.kind = 22;		 strcpy(token.str, "[");
			return token;
		case 62:
			token.kind = 23;
			strcpy(token.str, "]");
			return token;

		case 63:
			token.kind = 24;		 strcpy(token.str, ":");
			return token;
		case 64:
			token.kind = 25;		 strcpy(token.str, ";");
			return token;
		case 65:
			token.kind = 26;		 strcpy(token.str, "\"");
			return token;
		case 66:
			token.kind = 27;		 strcpy(token.str, "'");
			return token;
		case 67:
			token.kind = 28;		 strcpy(token.str, "#");
			return token;
		case 68:
			c = fgetc(fps);
			if (c == '|') 	state = 69;
			else 	 state = 70;
			break;
		case 69:
			token.kind = 2;	strcpy(token.sub_kind, "OR");	 strcpy(token.str, "||");
			return token;
		case 70:
			ungetc(c, fps);
			token.kind = 29;	 strcpy(token.str, "|");
			return token;
		case 71:
			token.kind = EOF_TOK; strcpy(token.str, "EOF");
			return token;
		case 72:
			ungetc(c, fps);
			token.kind = 6; strcpy(token.str, "/");
			return token;
		case 73:
			token.kind = 6; strcpy(token.str, "/");
			return token;
		case 74:
			c = fgetc(fps);
			if (c == '\n') state = 0;
			else if (c == EOF) state = 71;
			else state = 74;
			break;
		case 75:
			c = fgetc(fps);
			if (c == '*') state = 76;
			else if (c == EOF) state = 71;
			else state = 75;
			break;
		case 76:
			c = fgetc(fps);
			if (c == '/') state = 0;
			else if (c == EOF) state = 71;
			else state = 75;
			break;
		default: printf("Unrecognizable token! Stop generating tokens.\n");
			token.kind = EOF_TOK; strcpy(token.str, "EOF_TOK");
			return token;
		} // switch
	} //while
}

sym get_next_token() {
	sym token;
	tokentype a_tok;
	a_tok = lexan();
	token.kind = 0;
	if (a_tok.kind == EOF_TOK) {
		token.no = MaxTerminal - 1;
		strcpy(token.str, Terminals_list[MaxTerminal - 1].str);
	}
	else {
		token.no = a_tok.kind;
		strcpy(token.str, a_tok.str);
	}
	return token;
}

ty_ptr_item_node closure(ty_ptr_item_node IS) {
	ty_ptr_item_node new_cs = NULL;
	ty_ptr_item_node curr = NULL;
	ty_ptr_item_node cursor = NULL;

	sym SymAfterDot;

	int r_num, d_num;
	int i_0 = 0;

	r_num = d_num = 0;
	curr = IS;

	while (curr) {
		r_num = curr->RuleNum;
		d_num = curr->DotNum;

		if (d_num >= rules[r_num].rleng) {
			curr = curr->link;
			continue;
		}
		else
			SymAfterDot = rules[r_num].rightside[d_num];

		if (!SymAfterDot.kind) {
			curr = curr->link;
			continue;
		}

		for (i_0 = 0; i_0 < totalNumberOfRules; i_0++) {
			if (rules[i_0].leftside.no != SymAfterDot.no)
				continue;

			new_cs = (ty_ptr_item_node)malloc(sizeof(type_item));

			new_cs->RuleNum = i_0;
			new_cs->DotNum = 0;
			new_cs->link = NULL;

			if (CheckExistItem(IS, new_cs)) {
				free(new_cs);
				continue;
			}

			cursor = getLastItem(IS);
			cursor->link = new_cs;
		}
		curr = curr->link;
	}
	return IS;
}

int CheckExistItem(ty_ptr_item_node cs_list, ty_ptr_item_node s_val) {
	ty_ptr_item_node cursor = cs_list;

	while (cursor) {
		if (cursor->RuleNum == s_val->RuleNum && cursor->DotNum == s_val->DotNum)
			return 1;
		cursor = cursor->link;
	}

	return 0;
}

ty_ptr_item_node getLastItem(ty_ptr_item_node cs_list) {
	ty_ptr_item_node cursor = cs_list;
	while (cursor) {
		if (cursor->link == NULL)
			return 1;
		cursor = cursor->link;
	}

	return 0;
}

ty_ptr_item_node GoTo(ty_ptr_item_node IS, sym sym_val) {
	int r_num, d_num;
	sym SymAfterDot;
	ty_ptr_item_node cursor = NULL;
	ty_ptr_item_node New_Item = NULL;
	ty_ptr_item_node Go_To_Result_List = NULL;
	ty_ptr_item_node i_cursor = NULL;
	ty_ptr_item_node temp_item = NULL;
	
	cursor = IS;
	while (cursor) {
		r_num = cursor->RuleNum;
		d_num = cursor->DotNum;

		if (d_num >= rules[r_num].rleng) {
			cursor = cursor->link;
			continue;
		}
		SymAfterDot = rules[r_num].rightside[d_num];

		if (!(SymAfterDot.kind == sym_val.kind && SymAfterDot.no == sym_val.no)) {
			cursor = cursor->link;
			continue;
		}

		New_Item = (ty_ptr_item_node)malloc(sizeof(type_item));
		New_Item->RuleNum = r_num;
		New_Item->DotNum = d_num + 1;
		New_Item->link = NULL;

		if (CheckExistItem(Go_To_Result_List, New_Item)) {
			free(New_Item);
			cursor = cursor->link;
			continue;
		}

		if (Go_To_Result_List == NULL) {
			Go_To_Result_List = New_Item;
		}
		else {
			temp_item = getLastItem(Go_To_Result_List);
			temp_item->link = New_Item;
		}

		cursor = cursor->link;
	}

	if (Go_To_Result_List)
		return closure(Go_To_Result_List);
	else
		return NULL;
}

void makeGotoGraph(ty_ptr_item_node IS_0) {
	int i_0, i_1, i_max;
	sym sym_temp;
	goto_set_ptr		result = NULL;
	state_node_ptr		State_Node_List_Header = NULL;
	state_node_ptr		state_cursor = NULL;
	state_node_ptr		To_state_node = NULL;
	Arc_node_ptr		Arc_List_Header = NULL;
	ty_ptr_item_node	To_item_list = NULL;

	State_Node_List_Header = makeStateNode();
	State_Node_List_Header->id = 0;
	State_Node_List_Header->item_cnt = itemListCounter(IS_0);
	Number_Of_States = 1;
	state_cursor = State_Node_List_Header;

	while (state_cursor) {
		for (i_0 = 0; i_0 < 2; i_0++) {
			i_max = i_0 ? MaxNonterminal : MaxTerminal - 1;
			for (i_1 = 0; i_1 < i_max; i_1++) {
				sym_temp.kind = i_0;
				sym_temp.no = i_1;
				To_item_list = GoTo(state_cursor->item_start, sym_temp);

				if (To_item_list) {
					To_state_node = Add_A_State_Node(State_Node_List_Header, To_item_list);
					Add_An_Arc(&Arc_List_Header, state_cursor->id, To_state_node->id, sym_temp);
				}
			}
		}
		state_cursor = state_cursor->next;
	}

	States_And_Arcs = (goto_set_ptr)malloc(sizeof(goto_set));
	States_And_Arcs->State_Node_List = State_Node_List_Header;
	States_And_Arcs->Arc_list = Arc_List_Header;
}

state_node_ptr Add_A_State_Node(state_node_ptr State_Node_List_Header, ty_ptr_item_node To_list) {
	int Number_Of_Items = 0;
	state_node_ptr	cursor = State_Node_List_Header;
	state_node_ptr	last_cursor = NULL;
	state_node_ptr	new_state_node = NULL;

	Number_Of_Items = itemListCounter(To_list);

	while (cursor) {
		if (cursor->item_cnt != Number_Of_Items) {
			last_cursor = cursor;
			cursor = cursor->next;
			continue;
		}

		int is_same = is_same_two_itemlists(cursor->item_start, To_list);
		if (is_same) {
			deleteTyPtrItemNode(To_list);
			return cursor;
		}

		last_cursor = cursor;
		cursor = cursor->next;
	}

	new_state_node = makeStateNode();
	Number_Of_States++;

	new_state_node->item_cnt = Number_Of_Items;
	new_state_node->item_start = To_list;
	new_state_node->id = last_cursor->id + 1;
	new_state_node->next = NULL;
	last_cursor->next = new_state_node;

	return new_state_node;
}

void Add_An_Arc(Arc_node_ptr *Arc_List_Header, int from_num, int to_num, sym Symbol) {
	Arc_node_ptr	Arc_cursor, Arc_last = NULL;
	Arc_node_ptr	Arc_new = NULL;
	int same_arc_exists = 0;

	Arc_new = makeArcNode();

	Arc_new->from_state = from_num;
	Arc_new->to_state = to_num;
	Arc_new->gram_sym = Symbol;
	Arc_new->link = NULL;

	if (*Arc_List_Header == NULL) {
		*Arc_List_Header = Arc_new;
		NumberOfArcs++;
		return;
	}

	Arc_cursor = *Arc_List_Header;
	while (Arc_cursor) {
		if (Arc_cursor->from_state == from_num && Arc_cursor->to_state == to_num
			&& Arc_cursor->gram_sym.kind == Symbol.kind && Arc_cursor->gram_sym.no == Symbol.no) {
			same_arc_exists = 1;
			break;
		}
		else {
			Arc_last = Arc_cursor;
			Arc_cursor = Arc_cursor->link;
		}
	}

	if (!same_arc_exists) {
		Arc_last->link = Arc_new;
		NumberOfArcs++;
	}
	else
		free(Arc_new);
}

int is_same_two_itemlists(ty_ptr_item_node list1, ty_ptr_item_node list2) {
	int I1, I2;
	I1 = itemListCounter(list1);
	I2 = itemListCounter(list2);
	ty_ptr_item_node p1 = list1, p2;
	if (I1 != I2)
		return 0;
	while (p1) {
		p2 = list2;
		int p1_exists_in_list2 = 0;

		while (p2) {
			if (p1->RuleNum == p2->RuleNum && p1->DotNum == p2->DotNum) {
				p1_exists_in_list2 = 1;
				break;
			}
			p2 = p2->link;
		}

		if (!p1_exists_in_list2)
			return 0;
		p1 = p1->link;
	}
	return 1;
}

state_node_ptr makeStateNode(void) {
	state_node_ptr cursor;
	cursor = (state_node_ptr)malloc(sizeof(state_node));
	cursor->id = -1;
	cursor->item_cnt = 0;
	cursor->item_start = NULL;
	cursor->next = NULL;

	return cursor;
}

Arc_node_ptr makeArcNode(void) {
	Arc_node_ptr cursor;

	cursor = (Arc_node_ptr)malloc(sizeof(Arc_node));

	cursor->from_state = -1;
	cursor->to_state = -1;
	cursor->gram_sym.kind = -1;
	cursor->gram_sym.no = -1;
	cursor->link = NULL;

	return cursor;
}

int itemListCounter(ty_ptr_item_node IS) {
	int cnt = 0;
	ty_ptr_item_node cursor = IS;
	
	while (cursor) {
		cnt++;
		cursor = cursor->link;
	}

	return cnt;
}

int deleteTyPtrItemNode(ty_ptr_item_node item_list) {
	ty_ptr_item_node item_next = NULL;
	ty_ptr_item_node item_cursor = item_list->link;

	while (item_cursor) {
		item_next = item_cursor->link;
		free(item_cursor);
		item_cursor = item_next;
	}
	
	free(item_list);
	return 0;
}

void printGotoGraph(goto_set_ptr gsp) {
	state_node_ptr State_Node_List_Header = gsp->State_Node_List;
	Arc_node_ptr item_list = gsp->Arc_list;
	char str[10];
	FILE *fpw;
	fpw = fopen("goto_graph.txt", "w");

	while (State_Node_List_Header) {
		fprintf(fpw, "ID[%2d] (%3d) : ", State_Node_List_Header->id, State_Node_List_Header->item_cnt);
		fitemListPrint(State_Node_List_Header->item_start, fpw);
		State_Node_List_Header = State_Node_List_Header->next;
	}

	printf("\nTotal number of states = %d\n", Number_Of_States);
	fprintf(fpw, "Total number of states = %d\n", Number_Of_States);

	fprintf(fpw, "\nGoto arcs:\nFrom   To  Symbol\n");
	while (item_list) {
		fprintf(fpw, "%4d %4d    ", item_list->from_state, item_list->to_state);
		if (item_list->gram_sym.kind == 0)
			strcpy(str, Terminals_list[item_list->gram_sym.no].str);
		else
			strcpy(str, Nonterminals_list[item_list->gram_sym.no].str);
		fprintf(fpw,"%s \n", str);

		item_list = item_list->link;
	}
	printf("Total number of arcs \ %d\n", NumberOfArcs);
	fprintf(fpw, "Total number of arcs \ %d\n", NumberOfArcs);
	fclose(fpw);
}

int findToStateNodeId(Arc_node_ptr arc_list, int from_id, sym symbol) {
	Arc_node_ptr cursor = arc_list;

	while (cursor) {
		if (cursor->from_state == from_id && cursor->gram_sym.kind == symbol.kind
			&& cursor->gram_sym.no == symbol.no)
			return cursor->to_state;
		cursor = cursor->link;
	}

	return -1;
}

void fitemListPrint(ty_ptr_item_node IS, FILE *fpw) {
	int i_0;
	int r_num, d_num;

	ty_ptr_item_node cursor = IS;

	while (cursor) {
		r_num = cursor->RuleNum;
		d_num = cursor->DotNum;

		fprintf(fpw, "%s -> ", Nonterminals_list[rules[r_num].leftside.no].str);
		for (i_0 = 0; i_0 < rules[r_num].rleng; i_0++) {
			if (i_0 == d_num)
				fprintf(fpw, ".  ");
			fprintf(fpw, "%s ", rules[r_num].rightside[i_0].kind ? Nonterminals_list[rules[r_num].rightside[i_0].no].str :
			Terminals_list[rules[r_num].rightside[i_0].no].str);
		}
		if (i_0 == d_num)
			fprintf(fpw, ".");
		if (!rules[r_num].rleng)
			fprintf(fpw, "ep");
		fprintf(fpw, "     ");
		cursor = cursor->link;
	}
	fprintf(fpw, "\n");
}

void Made_Action_Table() {
	int to_state_id = -1;
	int i_0 = 0;
	state_node_ptr state_cursor = States_And_Arcs->State_Node_List;
	ty_ptr_item_node item_cursor = NULL;
	sym symbol;

	Clear_Action_Table();
	while (state_cursor) {
		item_cursor = state_cursor->item_start;

		while (item_cursor) {
			symbol = rules[item_cursor->RuleNum].rightside[item_cursor->DotNum];
			if (rules[item_cursor->RuleNum].rleng > item_cursor->DotNum) {
				to_state_id = findToStateNodeId(States_And_Arcs->Arc_list, state_cursor->id, symbol);

				if (to_state_id == -1) {
					printf("Logic error at Make_Action (1 ) \n");
					getchar();
				}

				if (Action_Table[state_cursor->id][symbol.no].Kind == 'e') {
					Action_Table[state_cursor->id][symbol.no].Kind = 's';
					Action_Table[state_cursor->id][symbol.no].num = to_state_id;
				}
				else {
					if (Action_Table[state_cursor->id][symbol.no].Kind == 's'
						&& Action_Table[state_cursor->id][symbol.no].num == to_state_id) {
					}
					else {
						printf("Make_Action_Table의 다중값 상황 발생1\n");
						getchar();
					}
				}
			}
			else {
				if (item_cursor->RuleNum == 0) {
					if (Action_Table[state_cursor->id][MaxTerminal - 1].Kind == 'e') {
						Action_Table[state_cursor->id][MaxTerminal - 1].Kind = 'a';
					}
					else {
						printf("Make_Action_Table의 다중값 상황발생2\n");
						getchar();
					}
				}
				else {
					for (i_0 = 0; i_0 < MaxTerminal; i_0++) {
						if (FollowTable[rules[item_cursor->RuleNum].leftside.no][i_0]) {
							if (Action_Table[state_cursor->id][i_0].Kind == 'e') {
								Action_Table[state_cursor->id][i_0].Kind = 'r';
								Action_Table[state_cursor->id][i_0].num = item_cursor->RuleNum;
							}
							else {
								if (Action_Table[state_cursor->id][i_0].Kind == 'r'
									&& Action_Table[state_cursor->id][i_0].num == item_cursor->RuleNum) {
								}
								else {
									printf("Make_Action_Table의 다중값 상황발생3\n");
									getchar();
								}
							}
						}
					}
				}
			}
			item_cursor = item_cursor->link;
		}
		state_cursor = state_cursor->next;
	}
}

void print_Action_Table(void) {
	int i_0, i_1;
	FILE *file_ptr = NULL;

	file_ptr = fopen("action_table.txt", "w");

	fprintf(file_ptr, "    \t");
	for (i_0 = 0; i_0 < MaxTerminal; i_0++) {
		fprintf(file_ptr, "%2s\t", Terminals_list[i_0].str);
	}
	fprintf(file_ptr, "\n");

	for (i_0 = 0; i_0 < Number_Of_States; i_0++) {
		fprintf(file_ptr, "%3d\t", i_0);
		for (i_1 = 0; i_1 < MaxTerminal; i_1++) {
			fprintf(file_ptr, "%c", Action_Table[i_0][i_1].Kind);
		}
	}


}