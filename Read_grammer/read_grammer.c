#define _CRT_SECURE_NO_WARNINGS

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#define Max_symbols 500
#define MaxRules 500

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

typedef struct twoints {
	int cr;
	int elm;
} element_stack;

int MaxTerminal;
int MaxNonterminal;
sym Nonterminals_list[Max_symbols];
sym Terminals_list[Max_symbols];

int totalNumberOfRules;
onerule rules[MaxRules];

int FirstTable[Max_symbols][Max_symbols];
int FollowTable[Max_symbols][Max_symbols];

void read_grammer(char *);
int lookUp_nonterminal(char *);
int lookUp_terminal(char *);
int Compute_first_of_one_nonterminal(sym);
int Compute_follow_of_one_nonterminal(int);
int Compute_first_of_any_string(sym[], int[]);


int main() {
	int i, j;
	sym a_nonterminal = { 1,0 };

	read_grammer("G_case2.txt");
	strcpy(Terminals_list[MaxTerminal].str, "epsilon");
	/*
	printf("NonTerminal : ");
	for (i = 0; i < MaxNonterminal; i++) {
		printf("%s ", Nonterminals_list[i].str);
	}
	printf("\n");
	printf("Terminal : ");
	for (i = 0; i < MaxTerminal + 1; i++) {
		printf("%s ", Terminals_list[i].str);
	}
	printf("\n\n");

	for (i = 0; i < totalNumberOfRules; i++) {
		printf("%s ->", rules[i].leftside.str);
		for (j = 0; j < 10; j++) {
			printf(" %s", rules[i].rightside[j].str);
		}
		printf("\n");
	} */
	

	for (i = 0; i < MaxNonterminal; i++) {
		for (j = 0; j < MaxTerminal + 1; j++) {
			FirstTable[i][j] = 0;
			FollowTable[i][j] = 0;
		}
		FirstTable[i][MaxTerminal + 1] = 0;
	}

	for (i = 0; i < MaxNonterminal; i++) {
		if (FirstTable[i][MaxTerminal + 1] == 0) {
			a_nonterminal.no = i;
			Compute_first_of_one_nonterminal(a_nonterminal);
		}
	}


	FollowTable[0][MaxTerminal - 1] = 1;
	for (i = 0; i < MaxNonterminal; i++) {
		if (FollowTable[i][MaxTerminal] == 0) {
			Compute_follow_of_one_nonterminal(i);
		}
	}



	for (i = 0; i < MaxNonterminal; i++) {
		printf("First(%s): ", Nonterminals_list[i].str);
		for (j = 0; j < MaxTerminal; j++) {
			if (FirstTable[i][j] == 1)
				printf("%s  ", Terminals_list[j].str);
		}
		if (FirstTable[i][MaxTerminal] == 1)
			printf("epsilon");
		printf("\n");
	}

	printf("\n");

	for (i = 0; i < MaxNonterminal; i++) {
		printf("Follow(%s): ", Nonterminals_list[i].str);
		for (j = 0; j < MaxTerminal; j++) {
			if (FollowTable[i][j] == 1)
				printf("%s  ", Terminals_list[j].str);
		}
		printf("\n");
	}

	printf("Program terminates.\n");
	return 0;
}

void read_grammer(char *fileName) {
	FILE *fp;
	char line[500];
	char symstr[10];
	char *ret;
	int i, k, n_sym, n_rule, i_leftSymbol, i_rightSymbol, i_right, synkind;

	fp = fopen(fileName, "r");
	if (!fp) {
		printf("File open error of grammer file.\n");
		getchar();
		return;
	}

	ret = fgets(line, 500, fp);
	ret = fgets(line, 500, fp);
	ret = fgets(line, 500, fp);
	
	i = 0;
	n_sym = 0;
	do {
		while (line[i] == ' ' || line[i] == '\t')
			i++;

		if (line[i] == '\n') break;
		k = 0;
		while (line[i] != ' ' && line[i] != '\t' && line[i] !='\n') {
			symstr[k] = line[i];
			i++;
			k++;
		}
		symstr[k] = '\0';
		strcpy(Nonterminals_list[n_sym].str, symstr);
		Nonterminals_list[n_sym].kind = 1;
		Nonterminals_list[n_sym].no = n_sym;
		n_sym++;
	} while (1);
	MaxNonterminal = n_sym;

	i = 0;
	n_sym = 0;

	ret = fgets(line, 500, fp);
	do {
		while (line[i] == ' ' || line[i] == '\t')
			i++;

		if (line[i] == '\n') break;
		k = 0;
		while (line[i] != ' ' && line[i] != '\t' && line[i] != '\n') {
			symstr[k] = line[i];
			i++;
			k++;
		}
		symstr[k] = '\0';
		strcpy(Terminals_list[n_sym].str, symstr);
		Terminals_list[n_sym].kind = 0;
		Terminals_list[n_sym].no = n_sym;
		n_sym++;
	} while (1);

	MaxTerminal = n_sym;

	ret = fgets(line, 500, fp);
	n_rule = 0;

	do {
		ret = fgets(line, 500, fp);
		if (!ret)
			break;

		i = 0;
		if (strlen(line) < 1)
			continue;
		else {
			while (line[i] == ' ' || line[i] == '\t')
				i++;
			if (!isalpha(line[i]))
				continue;
		}

		while (line[i] == ' ' || line[i] == '\t')
			i++;
		k = 0;
		while (line[i] != ' ' && line[i] != '\t' && line[i] != '\n') {
			symstr[k] = line[i];
			i++;
			k++;
		}
		symstr[k] = '\0';
		i_leftSymbol = lookUp_nonterminal(symstr);
		if (i_leftSymbol < 0) {
			printf("Wrong left symbol of a rule.\n");
			getchar();
		}

		rules[n_rule].leftside.kind = 1;
		rules[n_rule].leftside.no = i_leftSymbol;
		strcpy(rules[n_rule].leftside.str, symstr);

		while (line[i] != '>')
			i++;
		i++;
		while (line[i] == ' ' || line[i] == '\t')
			i++;

		i_right = 0;
		do {
			k = 0;
			
			while (i < strlen(line) && (line[i] != ' ' && line[i] != '\t' && line[i] != '\n')) {
				symstr[k] = line[i];
				i++;
				k++;
			}
			symstr[k] = '\0';
			if (strcmp(symstr, "epsilon") == 0) {
				rules[n_rule].rleng = 0;
				break;
			}

			if (isupper(symstr[0])) {
				synkind = 1;
				i_rightSymbol = lookUp_nonterminal(symstr);
			}
			else {
				synkind = 0;
				i_rightSymbol = lookUp_terminal(symstr);
			}

			if (i_rightSymbol < -1) {
				printf("Wrong right symbol of a rule.\n");
				getchar();
			}

			rules[n_rule].rightside[i_right].kind = synkind;
			rules[n_rule].rightside[i_right].no = i_rightSymbol;
			strcpy(rules[n_rule].rightside[i_right].str, symstr);

			i_right++;

			while ((line[i] == ' ') || (line[i] == '\t'))
				i++;
			if ((i >= strlen(line)) || (line[i] == '\n'))
				break;
		} while (1);

		rules[n_rule].rleng = i_right;
		n_rule++;
	} while (1);

	totalNumberOfRules = n_rule;
	printf("Total number of rules = %d\n", totalNumberOfRules);
}

int lookUp_nonterminal(char *str) {
	int i;
	for (i = 0; i < MaxNonterminal; i++)
		if (strcmp(str, Nonterminals_list[i].str) == 0)
			return i;

	return -1;
}

int lookUp_terminal(char *str) {
	int i;
	for (i = 0; i < MaxTerminal; i++)
		if (strcmp(str, Terminals_list[i].str) == 0)
			return i;

	return -1;
}

int Compute_first_of_one_nonterminal(sym X) {
	int i, j, k;
	int CR = -1;
	int Yi_has_epsilon;
	int first_result[Max_symbols];

	for (i = 0; i < MaxTerminal + 2; i++)
		first_result[i] = 0;

Next_Rule:
	CR++;
	if (CR >= totalNumberOfRules) {
		for (k = 0; k < MaxTerminal + 1; k++) {
			if (first_result[k] == 1)
				FirstTable[X.no][k] = 1;
		}
		FirstTable[X.no][MaxTerminal + 1] = 1;
		return 1;
	}

	if (!(rules[CR].leftside.kind == 1 && rules[CR].leftside.no == X.no))
		goto Next_Rule;

	if (rules[CR].rleng == 0) {
		first_result[MaxTerminal] = 1;
		goto Next_Rule;
	}

	i = 0;

Next_Element:
	if (rules[CR].rightside[i].kind == 0) {
		first_result[rules[CR].rightside[i].no] = 1;
		goto Next_Rule;
	}

	Yi_has_epsilon = 0;

	if (rules[CR].rightside[i].no != X.no) {
		if (FirstTable[rules[CR].rightside[i].no][MaxTerminal + 1] != 1)
			Compute_first_of_one_nonterminal(rules[CR].rightside[i]);

		for (k = 0; k < MaxTerminal; k++) {
			if (FirstTable[rules[CR].rightside[i].no][k] == 1)
				first_result[k] = 1;
			if (FirstTable[rules[CR].rightside[i].no][MaxTerminal] == 1)
				Yi_has_epsilon = 1;
		}
	}
	else {
		if (first_result[MaxTerminal] == 1)
			Yi_has_epsilon = 1;
	}

	if (Yi_has_epsilon == 0)
		goto Next_Rule;

	if (i == (rules[CR].rleng - 1)) {
		first_result[MaxTerminal] = 1;
		goto Next_Rule;
	}
	else {
		i++;
		goto Next_Element;
	}

	return 1;
}


int Compute_follow_of_one_nonterminal(int idx_NT) {
	int i, j, k, m;
	int first_result[Max_symbols]; // one row of First table.
	sym SymString[10];

	for (i = 0; i < totalNumberOfRules; i++) {
		for (j = 0; j < rules[i].rleng; j++)
		{    //  the symbol of index j of the RHS of rule i is to be processed in this iteration
			if (rules[i].rightside[j].kind == 0 || rules[i].rightside[j].no != idx_NT) continue; // skip this symbol j.
			// Now, position j has a nonterminal which is equal to idx_NT.
			if (j < rules[i].rleng - 1) {  // there are symbols after position j in RHS of rule i.
				m = 0;
				for (k = j + 1; k < rules[i].rleng; k++, m++)
					SymString[m] = rules[i].rightside[k];
				SymString[m].kind = -1;  // end of string marker.
				Compute_first_of_any_string(SymString, first_result); // Compute the first of the string after position j of rule i.
				for (k = 0; k < MaxTerminal; k++) // Copy the first symbols of the remaining string to the Follow of idx_NT.
					if (first_result[k] == 1) 
						FollowTable[idx_NT][k] = 1;
			}

			if (j == rules[i].rleng - 1 || first_result[MaxTerminal] == 1) // j is last symbol or first result has epsilon
			{
				if (rules[i].leftside.no == idx_NT) continue; // No need of adding the follow of the left side symbol
				if (FollowTable[rules[i].leftside.no][MaxTerminal] == 0) // We need follow of the left side sym of rule i.
					Compute_follow_of_one_nonterminal(rules[i].leftside.no);
				for (k = 0; k < MaxTerminal; k++) // add follow of left side symbol to follow of idx_NT.
					if (FollowTable[rules[i].leftside.no][k] == 1) 
						FollowTable[idx_NT][k] = 1;
			}
		} // end of for j=0.
	} // end of for i
	FollowTable[idx_NT][MaxTerminal] = 1;  // put the completion mark for this nonterminal.

	return 1;
} // end of function Compute_follow_of_one_nonterminal.

int Compute_first_of_any_string(sym alpha[], int first_result[]) {
	int i, k;
	for (i = 0; i < MaxTerminal + 2; i++)
		first_result[i] = 0; // initialize the first result of alpha

	// Let alpha be Y0 Y1 ... Yn-1
	i = 0;
	do {
		if (alpha[i].kind == 0) {  // Yi is terminal
			first_result[alpha[i].no] = 1;
			break;
		}
		else if (alpha[i].kind == 1) { // Yi is nonterminal
			for (k = 0; k < MaxTerminal; k++)	 // copy first of Yi to first of alpha
				if (FirstTable[alpha[i].no][k] == 1) 
					first_result[k] = 1;
			if (FirstTable[alpha[i].no][MaxTerminal] == 0)
				break; // first of Yi does not have epsilon.	
			else
				i = i + 1; // move to next Yi.
		}
		else if (alpha[i].kind == -1) {  // end of string mark.
			first_result[MaxTerminal] = 1; // if control reach here, all Yi's have epsilon in its first. Thus alpha has epsilon as first.
			break;
		}
	} while (1);
	return 1; // the first of alpha is passed thru parameter first_result.
} // end of function Compute_first_of_any_string