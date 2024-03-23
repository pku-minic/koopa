#ifndef LIBKOOPA_KOOPA_H_
#define LIBKOOPA_KOOPA_H_

#include <stddef.h>
#include <stdint.h>
#if defined(_WIN32) || defined(_WIN64)
#define KOOPA_OS_WINDOWS
#include <Windows.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

///
/// Error code of some Koopa functions.
///
enum koopa_error_code {
  /// No errors occurred.
  KOOPA_EC_SUCCESS = 0,
  /// UTF-8 string conversion error.
  KOOPA_EC_INVALID_UTF8_STRING,
  /// File operation error.
  KOOPA_EC_INVALID_FILE,
  /// Koopa IR program parsing error.
  KOOPA_EC_INVALID_KOOPA_PROGRAM,
  /// IO operation error.
  KOOPA_EC_IO_ERROR,
  /// Byte array to C string conversion error.
  KOOPA_EC_NULL_BYTE_ERROR,
  /// Insufficient buffer length.
  KOOPA_EC_INSUFFICIENT_BUFFER_LENGTH,
  /// Mismatch of item kind in raw slice.
  KOOPA_EC_RAW_SLICE_ITEM_KIND_MISMATCH,
  /// Passing null pointers to `libkoopa`.
  KOOPA_EC_NULL_POINTER_ERROR,
  /// Mismatch of type.
  KOOPA_EC_TYPE_MISMATCH,
  /// Mismatch of function parameter number.
  KOOPA_EC_FUNC_PARAM_NUM_MISMATCH,
};

///
/// Type of error code.
///
typedef enum koopa_error_code koopa_error_code_t;

///
/// Raw file (file descriptor or handle).
///
#ifdef KOOPA_OS_WINDOWS
typedef HANDLE koopa_raw_file_t;
#else
typedef int koopa_raw_file_t;
#endif

///
/// Koopa IR program.
///
typedef const void *koopa_program_t;

///
/// Raw program builder.
///
typedef void *koopa_raw_program_builder_t;

///
/// Kind of raw slice item.
///
enum koopa_raw_slice_item_kind {
  /// Unknown.
  KOOPA_RSIK_UNKNOWN = 0,
  /// Type.
  KOOPA_RSIK_TYPE,
  /// Function.
  KOOPA_RSIK_FUNCTION,
  /// Basic block.
  KOOPA_RSIK_BASIC_BLOCK,
  /// Value.
  KOOPA_RSIK_VALUE,
};

///
/// Type of raw slice item kind.
///
typedef enum koopa_raw_slice_item_kind koopa_raw_slice_item_kind_t;

///
/// A raw slice that can store any kind of items.
///
typedef struct {
  /// Buffer of slice items.
  const void **buffer;
  /// Length of slice.
  uint32_t len;
  /// Kind of slice items.
  koopa_raw_slice_item_kind_t kind;
} koopa_raw_slice_t;

///
/// Tag of raw Koopa type.
///
typedef enum {
  /// 32-bit integer.
  KOOPA_RTT_INT32,
  /// Unit (void).
  KOOPA_RTT_UNIT,
  /// Array (with base type and length).
  KOOPA_RTT_ARRAY,
  /// Pointer (with base type).
  KOOPA_RTT_POINTER,
  /// Function (with parameter types and return type).
  KOOPA_RTT_FUNCTION,
} koopa_raw_type_tag_t;

///
/// Kind of raw Koopa type.
///
typedef struct koopa_raw_type_kind {
  koopa_raw_type_tag_t tag;
  union {
    struct {
      const struct koopa_raw_type_kind *base;
      size_t len;
    } array;
    struct {
      const struct koopa_raw_type_kind *base;
    } pointer;
    struct {
      koopa_raw_slice_t params;
      const struct koopa_raw_type_kind *ret;
    } function;
  } data;
} koopa_raw_type_kind_t;

///
/// A raw Koopa type.
///
typedef const koopa_raw_type_kind_t *koopa_raw_type_t;

///
/// A raw Koopa program.
///
typedef struct {
  /// Global values (global allocations only).
  koopa_raw_slice_t values;
  /// Function definitions.
  koopa_raw_slice_t funcs;
} koopa_raw_program_t;

///
/// Data of raw Koopa function.
///
typedef struct {
  /// Type of function.
  koopa_raw_type_t ty;
  /// Name of function.
  const char *name;
  /// Parameters.
  koopa_raw_slice_t params;
  /// Basic blocks, empty if is a function declaration.
  koopa_raw_slice_t bbs;
} koopa_raw_function_data_t;

///
/// A raw Koopa function.
///
typedef const koopa_raw_function_data_t *koopa_raw_function_t;

///
/// Data of raw Koopa basic block.
///
typedef struct {
  /// Name of basic block, null if no name.
  const char *name;
  /// Parameters.
  koopa_raw_slice_t params;
  /// Values that this basic block is used by.
  koopa_raw_slice_t used_by;
  /// Instructions in this basic block.
  koopa_raw_slice_t insts;
} koopa_raw_basic_block_data_t;

///
/// A raw Koopa basic block.
///
typedef const koopa_raw_basic_block_data_t *koopa_raw_basic_block_t;

struct koopa_raw_value_data;

///
/// Data of raw Koopa value.
///
typedef struct koopa_raw_value_data koopa_raw_value_data_t;

///
/// A raw Koopa value.
///
typedef const koopa_raw_value_data_t *koopa_raw_value_t;

///
/// Raw integer constant.
///
typedef struct {
  /// Value of integer.
  int32_t value;
} koopa_raw_integer_t;

///
/// Raw aggregate constant.
///
typedef struct {
  /// Elements.
  koopa_raw_slice_t elems;
} koopa_raw_aggregate_t;

///
/// Raw function argument reference.
///
typedef struct {
  /// Index.
  size_t index;
} koopa_raw_func_arg_ref_t;

///
/// Raw basic block argument reference.
///
typedef struct {
  /// Index.
  size_t index;
} koopa_raw_block_arg_ref_t;

///
/// Raw global memory allocation.
///
typedef struct {
  /// Initializer.
  koopa_raw_value_t init;
} koopa_raw_global_alloc_t;

///
/// Raw memory load.
///
typedef struct {
  /// Source.
  koopa_raw_value_t src;
} koopa_raw_load_t;

///
/// Raw memory store.
///
typedef struct {
  /// Value.
  koopa_raw_value_t value;
  /// Destination.
  koopa_raw_value_t dest;
} koopa_raw_store_t;

///
/// Raw pointer calculation.
///
typedef struct {
  /// Source.
  koopa_raw_value_t src;
  /// Index.
  koopa_raw_value_t index;
} koopa_raw_get_ptr_t;

///
/// Raw element pointer calculation.
///
typedef struct {
  /// Source.
  koopa_raw_value_t src;
  /// Index.
  koopa_raw_value_t index;
} koopa_raw_get_elem_ptr_t;

///
/// Raw binary operator.
///
enum koopa_raw_binary_op {
  /// Not equal to.
  KOOPA_RBO_NOT_EQ,
  /// Equal to.
  KOOPA_RBO_EQ,
  /// Greater than.
  KOOPA_RBO_GT,
  /// Less than.
  KOOPA_RBO_LT,
  /// Greater than or equal to.
  KOOPA_RBO_GE,
  /// Less than or equal to.
  KOOPA_RBO_LE,
  /// Addition.
  KOOPA_RBO_ADD,
  /// Subtraction.
  KOOPA_RBO_SUB,
  /// Multiplication.
  KOOPA_RBO_MUL,
  /// Division.
  KOOPA_RBO_DIV,
  /// Modulo.
  KOOPA_RBO_MOD,
  /// Bitwise AND.
  KOOPA_RBO_AND,
  /// Bitwise OR.
  KOOPA_RBO_OR,
  /// Bitwise XOR.
  KOOPA_RBO_XOR,
  /// Shift left logical.
  KOOPA_RBO_SHL,
  /// Shift right logical.
  KOOPA_RBO_SHR,
  /// Shift right arithmetic.
  KOOPA_RBO_SAR,
};

///
/// Type of raw binary operator.
///
typedef enum koopa_raw_binary_op koopa_raw_binary_op_t;

///
/// Raw binary operation.
///
typedef struct {
  /// Operator.
  koopa_raw_binary_op_t op;
  /// Left-hand side value.
  koopa_raw_value_t lhs;
  /// Right-hand side value.
  koopa_raw_value_t rhs;
} koopa_raw_binary_t;

///
/// Raw conditional branch.
///
typedef struct {
  /// Condition.
  koopa_raw_value_t cond;
  /// Target if condition is `true`.
  koopa_raw_basic_block_t true_bb;
  /// Target if condition is `false`.
  koopa_raw_basic_block_t false_bb;
  /// Arguments of `true` target..
  koopa_raw_slice_t true_args;
  /// Arguments of `false` target..
  koopa_raw_slice_t false_args;
} koopa_raw_branch_t;

///
/// Raw unconditional jump.
///
typedef struct {
  /// Target.
  koopa_raw_basic_block_t target;
  /// Arguments of target..
  koopa_raw_slice_t args;
} koopa_raw_jump_t;

///
/// Raw function call.
///
typedef struct {
  /// Callee.
  koopa_raw_function_t callee;
  /// Arguments.
  koopa_raw_slice_t args;
} koopa_raw_call_t;

///
/// Raw function return.
///
typedef struct {
  /// Return value, null if no return value.
  koopa_raw_value_t value;
} koopa_raw_return_t;

///
/// Tag of raw Koopa value.
///
typedef enum {
  /// Integer constant.
  KOOPA_RVT_INTEGER,
  /// Zero initializer.
  KOOPA_RVT_ZERO_INIT,
  /// Undefined value.
  KOOPA_RVT_UNDEF,
  /// Aggregate constant.
  KOOPA_RVT_AGGREGATE,
  /// Function argument reference.
  KOOPA_RVT_FUNC_ARG_REF,
  /// Basic block argument reference.
  KOOPA_RVT_BLOCK_ARG_REF,
  /// Local memory allocation.
  KOOPA_RVT_ALLOC,
  /// Global memory allocation.
  KOOPA_RVT_GLOBAL_ALLOC,
  /// Memory load.
  KOOPA_RVT_LOAD,
  /// Memory store.
  KOOPA_RVT_STORE,
  /// Pointer calculation.
  KOOPA_RVT_GET_PTR,
  /// Element pointer calculation.
  KOOPA_RVT_GET_ELEM_PTR,
  /// Binary operation.
  KOOPA_RVT_BINARY,
  /// Conditional branch.
  KOOPA_RVT_BRANCH,
  /// Unconditional jump.
  KOOPA_RVT_JUMP,
  /// Function call.
  KOOPA_RVT_CALL,
  /// Function return.
  KOOPA_RVT_RETURN,
} koopa_raw_value_tag_t;

///
/// Kind of raw Koopa value.
///
typedef struct {
  koopa_raw_value_tag_t tag;
  union {
    koopa_raw_integer_t integer;
    koopa_raw_aggregate_t aggregate;
    koopa_raw_func_arg_ref_t func_arg_ref;
    koopa_raw_block_arg_ref_t block_arg_ref;
    koopa_raw_global_alloc_t global_alloc;
    koopa_raw_load_t load;
    koopa_raw_store_t store;
    koopa_raw_get_ptr_t get_ptr;
    koopa_raw_get_elem_ptr_t get_elem_ptr;
    koopa_raw_binary_t binary;
    koopa_raw_branch_t branch;
    koopa_raw_jump_t jump;
    koopa_raw_call_t call;
    koopa_raw_return_t ret;
  } data;
} koopa_raw_value_kind_t;

struct koopa_raw_value_data {
  /// Type of value.
  koopa_raw_type_t ty;
  /// Name of value, null if no name.
  const char *name;
  /// Values that this value is used by.
  koopa_raw_slice_t used_by;
  /// Kind of value.
  koopa_raw_value_kind_t kind;
};

///
/// Parses text-form Koopa IR program from the given file.
/// Updates the `program` if no errors occurred.
///
/// Returns the error code.
///
koopa_error_code_t koopa_parse_from_file(const char *path,
                                         koopa_program_t *program);

///
/// Parses text-form Koopa IR program from the given string.
/// Updates the `program` if no errors occurred.
///
/// Returns the error code.
///
koopa_error_code_t koopa_parse_from_string(const char *str,
                                           koopa_program_t *program);

///
/// Parses text-form Koopa IR program from the standard input.
/// Updates the `program` if no errors occurred.
///
/// Returns the error code.
///
koopa_error_code_t koopa_parse_from_stdin(koopa_program_t *program);

///
/// Parses text-form Koopa IR program from the given
/// file descriptor (UNIX) or handle (Windows).
/// Updates the `program` if no errors occurred.
///
/// Returns the error code.
///
koopa_error_code_t koopa_parse_from_raw(koopa_raw_file_t file,
                                        koopa_program_t *program);

///
/// Deletes the given program.
///
/// All programs returned by Koopa IR library functions
/// should be deleted manually.
///
void koopa_delete_program(koopa_program_t program);

///
/// Generates text-form Koopa IR program to the given file.
///
/// Returns the error code.
///
koopa_error_code_t koopa_dump_to_file(koopa_program_t program,
                                      const char *path);

///
/// Generates a null-terminated string of text-form Koopa IR program
/// to the given buffer. If the given buffer is null, updates the `len`
/// to the length of the generated string (with out the null-terminator).
///
/// Returns the error code.
///
koopa_error_code_t koopa_dump_to_string(koopa_program_t program,
                                        char *buffer, size_t *len);

///
/// Generates text-form Koopa IR program to the standard output.
///
/// Returns the error code.
///
koopa_error_code_t koopa_dump_to_stdout(koopa_program_t program);

///
/// Generates text-form Koopa IR program to the given
/// file descriptor (UNIX) or handle (Windows).
///
/// Returns the error code.
///
koopa_error_code_t koopa_dump_to_raw(koopa_program_t program,
                                     koopa_raw_file_t file);

///
/// Generates LLVM IR to the given file.
///
/// Returns the error code.
///
koopa_error_code_t koopa_dump_llvm_to_file(koopa_program_t program,
                                           const char *path);

///
/// Generates a null-terminated string of LLVM IR to the given buffer.
/// If the given buffer is null, updates the `len` to the length of
/// the generated string (with out the null-terminator).
///
/// Returns the error code.
///
koopa_error_code_t koopa_dump_llvm_to_string(koopa_program_t program,
                                             char *buffer, size_t *len);

///
/// Generates LLVM IR to the standard output.
///
/// Returns the error code.
///
koopa_error_code_t koopa_dump_llvm_to_stdout(koopa_program_t program);

///
/// Generates LLVM IR to the given
/// file descriptor (UNIX) or handle (Windows).
///
/// Returns the error code.
///
koopa_error_code_t koopa_dump_llvm_to_raw(koopa_program_t program,
                                          koopa_raw_file_t file);

///
/// Creates a new raw program builder. Returns its pointer.
///
koopa_raw_program_builder_t koopa_new_raw_program_builder();

///
/// Frees allocated memory of the given raw program builder.
///
void koopa_delete_raw_program_builder(koopa_raw_program_builder_t builder);

///
/// Builds a raw program of the given Koopa IR program
/// using the given raw program builder.
///
/// The generated raw program is valid iff the raw program builder
/// is still alive (not deleted). The generated raw program should
/// not be modified manually.
///
koopa_raw_program_t koopa_build_raw_program(
    koopa_raw_program_builder_t builder, koopa_program_t program);

///
/// Generates the given raw program to the Koopa IR program.
/// Updates the `program` if no errors occurred.
///
/// Returns the error code.
///
koopa_error_code_t koopa_generate_raw_to_koopa(
    const koopa_raw_program_t *raw, koopa_program_t *program);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // LIBKOOPA_KOOPA_H_
