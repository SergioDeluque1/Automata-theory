#include <iostream>
#include <limits>

int main() {
    // Integer types
    int int_max = std::numeric_limits<int>::max();
    int int_min = std::numeric_limits<int>::min();
    unsigned int uint_max = std::numeric_limits<unsigned int>::max();
    unsigned int uint_min = std::numeric_limits<unsigned int>::min();

    // Floating point types
    float float_max = std::numeric_limits<float>::max();
    float float_min = std::numeric_limits<float>::min();
    float float_lowest = std::numeric_limits<float>::lowest();

    // Display initial values
    std::cout << "Initial Values:\n";
    std::cout << "int_max: " << int_max << "\n";
    std::cout << "int_min: " << int_min << "\n";
    std::cout << "uint_max: " << uint_max << "\n";
    std::cout << "uint_min: " << uint_min << "\n";
    std::cout << "float_max: " << float_max << "\n";
    std::cout << "float_min: " << float_min << "\n";
    std::cout << "float_lowest: " << float_lowest << "\n";

    // Induce overflow and underflow
    int_max += 1;
    int_min -= 1;
    uint_max += 1;
    float_max *= 2.0f;
    float_min /= 2.0f;
    float_lowest *= 2.0f;

    // Display modified values
    std::cout << "After Overflow/Underflow:\n";
    std::cout << "int_max: " << int_max << "\n";
    std::cout << "int_min: " << int_min << "\n";
    std::cout << "uint_max: " << uint_max << "\n";
    std::cout << "uint_min: " << uint_min << "\n";
    std::cout << "float_max: " << float_max << "\n";
    std::cout << "float_min: " << float_min << "\n";
    std::cout << "float_lowest: " << float_lowest << "\n";

    return 0;
}
