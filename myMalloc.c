#include <errno.h>

#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

//char freelist_bitmap[7]={0,0,0,0,0,0,0};

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

static inline header * find_freelist(size_t block_size);
static inline header * split_block(header * cur, size_t block_size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}


header * get_freelist(size_t size)
{
  size_t size_to_index = (((size | sizeof(size_t) - 1) - ALLOC_HEADER_SIZE) >> 3) - 2;
  if (size_to_index > 58) {
    size_to_index = 58;
  }

  size_t next_set_index = size_to_index;
  while (next_set_index < 59) {
    header * freelist = &freelistSentinels[next_set_index];
    if (freelist->next != freelist) {
        return &freelistSentinels[next_set_index];
    }
    next_set_index++;
  }

}


void freelist_insert_between(header *block, header *prev, header *next)
{
  block->next = next;
  block->prev = prev;
  next->prev = block;
  prev->next = block;
}

void freelist_insert(header *block)
{
  size_t size = get_size(block);
  size_t index = (((size | (sizeof(size_t) - 1)) - ALLOC_HEADER_SIZE) >> 3) - 2;
  if (index > 58) {
    index = 58;
  }

  header *freelist = &freelistSentinels[index];
  freelist_insert_between(block, freelist->prev, freelist);
}

void freelist_remove(header *block)
{
  block->prev->next = block->next;
  block->next->prev = block->prev;
}

void move_coalesced(header *block, size_t oldSize)
{
  freelist_remove(block);
  freelist_insert(block);
}

void coalesce_right(header *block, header *right)
{
  set_state(block, UNALLOCATED);
  header * right_block = get_right_header(right);
  right_block->left_size = get_size(block) + get_size(right);
  set_size(block, get_size(block) + get_size(right));

  right->next->prev = right->prev;
  right->prev->next = right->next;
  freelist_insert(block);
}

void coalesce_left(header *left, header *block, header *right)
{
  size_t size;
  size_t newSize;
  size_t oldSize;

  oldSize = get_size(left);
  size = get_size(left);
  newSize = size + get_size(block);
  set_size(left, newSize);
  right->left_size = get_size(left);
  freelist_remove(left);
  freelist_insert(left);
}

void coalesce_both(header *left, header *block, header *right)
{
  size_t size;
  size_t newSize;
  header *rightRight;
  size_t oldSize;

  rightRight = get_right_header(right);
  oldSize = get_size(left);
  size = get_size(left);
  newSize = get_size(block) + size + get_size(right);
  set_size(left, newSize);
  rightRight->left_size = get_size(left);
  freelist_remove(right);
  freelist_remove(left);
  freelist_insert(left);
}

void free_list_deallocate(header *block)
{
  header *left;
  header *right;

  left = get_left_header(block);
  right = get_right_header(block);
  if ( get_state(left) && get_state(right) )
  {
    freelist_insert(block);
  }
  else if ( get_state(left) || get_state(right) )
  {
    if ( get_state(left) )
    {
      if ( get_state(right) == UNALLOCATED )
        coalesce_right(block, right);
    }
    else
    {
      coalesce_left(left, block, right);
    }
  }
  else
  {
    coalesce_both(left, block, right);
  }
}


/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);

  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation

  header *newChunk;
  header *prevFencePost;
  header *rightFence;
  size_t chunkSize;
  size_t sizeFence;
  header *header_from_offset;
  header *block;

  if ( !raw_size )
    return NULL;
  size_t block_size = ((raw_size + ((sizeof(size_t) - 1) + ALLOC_HEADER_SIZE)) / sizeof(size_t)) * sizeof(size_t);
  if ( block_size < 2 * ALLOC_HEADER_SIZE)
    block_size = 2 * ALLOC_HEADER_SIZE;


  block = find_freelist(block_size);
  if ( block ) {
    return block;
  }

  while (block == NULL) {
    newChunk = allocate_chunk(ARENA_SIZE);
    if ( !newChunk )
      return NULL;
    prevFencePost = get_header_from_offset(newChunk, (-2 * ALLOC_HEADER_SIZE));
    chunkSize = get_size(newChunk);
    rightFence = get_header_from_offset(newChunk, chunkSize);
    if ( prevFencePost == lastFencePost )
    {
      sizeFence = get_size(newChunk) + (2 * ALLOC_HEADER_SIZE);
      set_size(prevFencePost, sizeFence);
      rightFence->left_size = get_size(prevFencePost);
      set_state(prevFencePost, UNALLOCATED);
      free_list_deallocate(prevFencePost);
    }
    else
    {
      freelist_insert(newChunk);
      header_from_offset = get_header_from_offset(newChunk, -ALLOC_HEADER_SIZE);
      insert_os_chunk(header_from_offset);
    }
    lastFencePost = rightFence;
    block = find_freelist(block_size);
  }

  return block;
}


/**
 * @brief Helper to find the appropriate free list
 * 
 * @param block_size including header
 * 
 * @return A pointer to the header of block
 */
static inline header * find_freelist(size_t size) {
  header * current;
  header * freelist;

  freelist = get_freelist(size);
  if (freelist->next == freelist) {
    return NULL;
  }
  for (current = freelist->next; ; current = current->next) {
    if (size <= get_size(current)) {
      break;
    }
  }
  if (get_size(current) >= (size + 2 * ALLOC_HEADER_SIZE)) {
    return split_block(current, size);
  }
  freelist_remove(current);
  set_state(current, ALLOCATED);

  return current;


}

/**
 * @brief Helper to split the block when necessary
 *
 * @param cur pointer points to current block
 * @param block_size including header
 *
 * @return A pointer to the block will be allocated
 */

static inline header * split_block(header * cur, size_t block_size) {
  size_t v2;
  size_t v3;
  header *right;
  header *remainder;

  get_size(cur);
  v2 = get_size(cur);
  right = get_header_from_offset(cur, v2);
  remainder = get_header_from_offset(cur, block_size);
  set_state(remainder, UNALLOCATED);
  v3 = get_size(cur) - block_size;
  set_size(remainder, v3);
  remainder->left_size = block_size;
  set_state(cur, ALLOCATED);
  set_size(cur, block_size);
  right->left_size = get_size(remainder);
  freelist_remove(cur);
  freelist_insert(remainder);
  return cur;
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */

static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  header * hdr = ptr_to_header(p);

  if (get_state(hdr) == UNALLOCATED) {
    fprintf(stderr, "Double Free Detected\n");
    assert(false);
    exit(1);
  }
  set_state(hdr, UNALLOCATED);

  free_list_deallocate(hdr);

}


/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next;
         fast != freelist;
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}

	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}

	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/*
 * External interface
 */
void * my_malloc(size_t size) {
  if (!size) {
    return NULL;
  }
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size);
  pthread_mutex_unlock(&mutex);
  if ( !hdr )
    return 0LL;
  set_state(hdr, ALLOCATED);
  return (header *)((char *)hdr + ALLOC_HEADER_SIZE);
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem;
}

void my_free(void * p) {
  if (p != NULL){
    pthread_mutex_lock(&mutex);
    deallocate_object(p);
    pthread_mutex_unlock(&mutex);
  }
}

bool verify() {
  return verify_freelist() && verify_tags();
}
