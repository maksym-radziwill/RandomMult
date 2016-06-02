/* Could it be that the multiplicative function defined by 
   f(2) = 1, f(3) = -1, f(5) = 1, f(7) = -1, f(11) = 1, ...
   exhibits more than square root cancellation ? */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>

#define BLOCK 4096 /* Size of a stack block */
// #define PRIME_SIEVE 1

#ifdef PRIME_SIEVE
#include <primesieve.h>
#endif

/* Sieve of Erathostenes */
/* This is only ran once to precompute the table of primes */

int * sieve (int n) {
  char * table = calloc(n + 1, sizeof(char));
  if(table == NULL){
    fprintf(stderr, "Could not allocate %d bytes for prime table\n", n + 1);
    exit(-1); 
  }
  
  memset(table, (char) 1, n + 1); 

  for(int i = 2; i <= n; i++)
    if(table[i] == 1)
      for(int j = 2*i; j <= n; j += i)
	table[j] = 0; 

  int num_primes = 0;
  for(int i = 2; i <= n; i++)
    if(table[i] == 1)
      num_primes += 1; 
  
  int * primes = calloc(num_primes + 1, sizeof(int));
  if(primes == NULL){
    fprintf(stderr, "Could not allocate %lld bytes for prime table\n", (long long) (num_primes + 1)*sizeof(int));
    exit(-1); 
  }
  
  int j = 0; 
  
  for(int i = 2; i <= n; i++)
    if(table[i] == 1){
      primes[j] = i;
      j = j + 1; 
    }

  free(table);

  return primes; 
}

int count_squarefree(int n, int * table){
  char * sqf = malloc((n+1)*sizeof(char));
  memset(sqf, (char) 1, n+1);
  for(int i = 0; table[i] != 0 && table[i] <= (int) sqrt(n); i++){
    for(int j = table[i]*table[i]; j <= n; j += table[i]*table[i])
      sqf[j] = (char) 0;
  }
  int sum = 0; 
  for(int i = 1; i <= n; i++)
    if(sqf[i] == (char) 1)
      sum += 1;
  free(sqf); 
  return sum;
}


/*

// This is the recursive algorithm that we use to generate the sum of random multiplicative function
// The drawback of the Recursive algorithm is that it crashes once the number of iterations exceeds the
// allowed size of the stack. For this reason the algorithm is unfolded into an iterative version below

int gen_mul(int n, int j, const int * table){
  if (n == 1) return 1;
  if (n <= 0) return 0;
  if (table[j] == 0) return 1; 
  if (table[j] > n) return 1;
  if (table[j] == n) return 0; // This line is special to the Liouville function and should be avoided
  return (gen_mul(n, j + 1,table) + rand_sign() * gen_mul(n/table[j], j + 1,table)); 
}

*/

struct stack {
  int n;
  int j; 
  int sign; 
};

struct Stack {
  struct stack * stk;
  int stack_size;
  int counter; 
};

struct Stack init_stack(){
  struct Stack stk; 
  stk.stk = malloc(BLOCK*sizeof(struct stack)); 
  if(stk.stk == NULL){
    fprintf(stderr, "Could not allocate %d bytes for the stack\n", BLOCK*sizeof(struct stack));
    exit(-1); 
  }
  stk.stack_size = BLOCK;
  stk.counter = 0;
  return stk; 
}

void free_stack(struct Stack * stk){
  free(stk->stk);
  stk->stack_size = 0; 
  stk->counter = 0; 
}

void push_stack(struct Stack * stk, struct stack s){
  if(stk->counter >= stk->stack_size){
    stk->stack_size += BLOCK; 
    stk->stk = realloc(stk->stk, stk->stack_size*sizeof(struct stack));
    if(stk->stk == NULL){
      fprintf(stderr, "Failed allocate %d more bytes on the stack (of size %lld bytes)\n",
	      BLOCK*sizeof(struct stack), (long long) (stk->stack_size - BLOCK)*sizeof(struct stack));
      exit(-1); 
    }
  }
  stk->stk[stk->counter] = s;
  stk->counter++;
}

struct stack pop_stack(struct Stack * stk){
  stk->counter--;
  struct stack result = stk->stk[stk->counter];
  if(stk->counter < stk->stack_size - BLOCK && stk->stack_size - BLOCK >= 0){
    stk->stack_size -= BLOCK;
    stk->stk = realloc(stk->stk, stk->stack_size*sizeof(struct stack));
    if(stk->stk == NULL){
      fprintf(stderr, "Failed dimishing (!) the stack size by %d bytes to a total of %lld bytes\n",
	      BLOCK*sizeof(struct stack), (long long) stk->stack_size*sizeof(struct stack));
      exit(-1); 
    }
  }
  return result; 
}

typedef struct { uint64_t state;  uint64_t inc; } pcg32_random_t;

int pcg32_random_r(pcg32_random_t * rng){
  uint64_t oldstate = rng->state;
  // Advance internal state
  rng->state = oldstate * 6364136223846793005ULL + (rng->inc|1);
  // Calculate output function (XSH RR), uses old state for max ILP
  uint32_t xorshifted = ((oldstate >> 18u) ^ oldstate) >> 27u;
  uint32_t rot = oldstate >> 59u;
  int num = (xorshifted >> rot) | (xorshifted << ((-rot) & 31));
  return num;
}

void seed_rng(pcg32_random_t* rng, uint64_t initstate, uint64_t initseq)
{
  rng->state = 0U;
  rng->inc = (initseq << 1u) | 1u;
  pcg32_random_r(rng);
  rng->state += initstate;
  pcg32_random_r(rng);
}


int rand_sign(pcg32_random_t * rng)
{
  int num = pcg32_random_r(rng); 
  if(num % 2 == 0) return 1;
  return -1; 
}

int gen_mul_new(int N, const int * table, struct Stack * Stk, int * rand_table){

  struct stack stk; 
  
  int sum = 0;
  int j, n, sign; 

  stk.j = 0;
  stk.n = N;
  stk.sign = 1; 
  push_stack(Stk,stk); 

  while(Stk->counter != 0){

    stk = pop_stack(Stk); 
    
    j = stk.j;
    n = stk.n;
    sign = stk.sign;
    
    if(n <= 0) continue;
    
    if(n == 1 || table[j] == 0 || table[j] > n) {
      sum += sign;
      continue; 
    }

    if(table[j] >  (int) sqrt(n)){
      int small_sum = 0;
      for(int l = j; table[l] <= n && table[l] != 0; l++)
	small_sum += rand_table[l]; 
      sum += sign*(1 + small_sum); 
      continue; 
    }
    
    stk.j = j + 1;
    stk.n = n;
    stk.sign = sign; 
    push_stack(Stk,stk);
    stk.n = n / table[j];
    stk.sign = rand_table[j]*sign; 
    push_stack(Stk,stk);    
  }
  
  return sum;  
}

struct thread_arg {
  int n;
  int samples;
  int num_primes; 
  int * table; 
  int state;
  int tid;
};

long long * thread(struct thread_arg * arg){
  struct Stack Stk = init_stack(); 
  long long result = 0;
  long long result2 = 0; 
  int * rand_table = malloc(arg->num_primes*sizeof(int)); 
  pcg32_random_t rng;
  seed_rng(&rng, (int) arg + arg->state, arg->state); 
  
  for(int i = 0; i < arg->samples; i++){
    int L = (int) sqrt(arg->samples); 
    if(i % L == 0){
      printf("\rThread %d: Sampling %d/%d ... ", arg->tid, i, arg->samples); fflush(stdout); 
    }

    for(int i = 0; i < arg->num_primes; i++) rand_table[i] = rand_sign(&rng);

    int new_value = abs(gen_mul_new(arg->n, arg->table, &Stk, rand_table)); 
    result += new_value; 
    result2 += new_value * new_value; 
    
  }

  free_stack(&Stk); 
  free(rand_table); 
  
  long long * res = malloc(2*sizeof(long long));
  res[0] = result;
  res[1] = result2; 
  
  return res; 
}

int * gen_prime_array(int n, int * num_primes){
  printf("Generating prime array ... "); fflush(stdout); 
#ifdef PRIME_SIEVE
  int * table = (int*) primesieve_generate_primes(0, n, num_primes, INT_PRIMES);
  table = realloc(table, (*num_primes+1)*sizeof(int));
  table[*num_primes] = 0;
#endif
#ifndef PRIME_SIEVE
  int * table = sieve(n);
  *num_primes = 0; 
  for(;table[*num_primes] != 0; (*num_primes) += 1); 
#endif
  printf("DONE\n"); fflush(stdout); 
  return table; 
}

int main(int argc, char ** argv){

  if(argc < 5){
    fprintf(stderr, "Usage: %s n samples seed num_threads\n", argv[0]);
    exit(0); 
  }

  int n = atoi(argv[1]);
  int samples = atoi(argv[2]); 
  int state = atoi(argv[3]);
  int num_threads = atoi(argv[4]); 

  int num_primes = 0; 
  int * table = gen_prime_array(n, &num_primes); 
  
  pthread_t * threads = malloc(num_threads*sizeof(pthread_t));
  long long ** results = malloc(num_threads*sizeof(long long *));

  struct thread_arg * arg = malloc(num_threads*sizeof(struct thread_arg)); 
  
  for(int i = 0; i < num_threads; i++){
    arg[i].n = n;
    arg[i].samples = (int) 1 + (samples / num_threads);
    arg[i].table = table;
    arg[i].state = state + i; 
    arg[i].num_primes = num_primes; 
    arg[i].tid = i;
    pthread_create(&threads[i], NULL, (void *) &thread, (void *) &arg[i]); 
  }

  samples = num_threads * (1 + (samples / num_threads)); 
  
  for(int i = 0; i < num_threads; i++)
    pthread_join(threads[i], (void **) &results[i]);

  printf("DONE\n"); 
  
  free(arg);
  free(threads); 
  
  long long result = 0;
  long long result2 = 0; 
  for(int i = 0; i < num_threads; i++){
    result += results[i][0];
    result2 += results[i][1]; 
  }

  for(int i = 0; i < num_threads; i++)
    free(results[i]);   
  free(results); 
  
  printf("Sum of %d samples : %lld\n", samples, result); 
  printf("Sum of %d samples (2nd moment) : %lld\n", samples, result2); 
  
  printf("Computing number of square-free integers ... "); fflush(stdout);
  int num_squarefree = count_squarefree(n, table);
  printf("DONE\n"); fflush(stdout); 

  free(table); 
  
  printf("Normalized estimate: %f\n", (float) result / (samples*sqrt(num_squarefree)));
  printf("Normalized estimate (2nd moment): %f\n", (float) result2 / (samples * num_squarefree)); 
  
  /* Could also compute the variance of the samples to make sure that it is not too large */
  
  return 0;
}
