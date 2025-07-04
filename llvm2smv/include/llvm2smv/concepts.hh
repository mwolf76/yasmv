#ifndef LLVM2SMV_CONCEPTS_H
#define LLVM2SMV_CONCEPTS_H

#include <concepts>
#include <type_traits>

namespace llvm2smv {

// C++20 concepts for better type safety and clearer interfaces

/// Concept for types that can be printed to an output stream
template<typename T>
concept Printable = requires(T t, llvm::raw_ostream& os) {
    t.print(os);
};

/// Concept for types that can be cloned
template<typename T>
concept Cloneable = requires(const T& t) {
    { t.clone() } -> std::same_as<std::unique_ptr<T>>;
};

/// Concept for SMV expression types
template<typename T>
concept SMVExprType = requires(T t) {
    requires std::derived_from<T, class SMVExpr>;
    requires Printable<T>;
    requires Cloneable<T>;
};

/// Concept for SMV type types
template<typename T>
concept SMVTypeType = requires(T t) {
    requires std::derived_from<T, class SMVType>;
    requires Printable<T>;
    requires Cloneable<T>;
    { t.getKind() } -> std::convertible_to<typename SMVType::TypeKind>;
};

/// Concept for integer-like values
template<typename T>
concept IntegerLike = std::integral<T> || std::same_as<T, int64_t>;

/// Concept for string-like values
template<typename T>
concept StringLike = std::convertible_to<T, std::string> ||
                     std::same_as<T, llvm::StringRef>;

} // namespace llvm2smv

#endif // LLVM2SMV_CONCEPTS_H
