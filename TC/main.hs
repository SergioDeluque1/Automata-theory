-- Definición de la función recursór 
natrec :: a -> (Integer -> a -> a) -> Integer -> a
natrec Base rstep 0 = Base
natrec Base rstep n = rstep n (natrec Base rstep (n - 1))

-- Función Factorial
factorial :: Integer -> Integer
factorial = natrec 1 (\n rec -> n * rec)

-- Sumatoria de los primeros N números
sumatoria :: Integer -> Integer
sumatoria = natrec 0 (\n rec -> n + rec)

-- Módulo de la división de dos números
modr :: Integer -> Integer -> Integer
modr b a = natrec a (\_ rec -> if rec >= b then rec - b else rec) a

-- Fibonacci
fibonacci :: Integer -> Integer
fibonacci n = natrec 0 (\k rec -> if k == 1 then 1 else if k == 2 then 1 else rec + fibonacci (k - 2)) n

-- Función main
main :: IO () —- mónada para el recibimiento de E/S
main = do
    putStrLn "Ingrese un número natural:"
    input <- getLine
    let n = read input :: Integer

    putStrLn $ "Factorial de " ++ show n ++ ":"
    print (factorial n)

    putStrLn $ "Sumatoria de los primeros " ++ show n ++ " números:"
    print (sumatoria n)

    putStrLn "Ingrese un número para calcular el módulo:"
    inputB <- getLine
    let b = read inputB :: Integer

    putStrLn $ "Módulo de " ++ show n ++ " dividido por " ++ show b ++ ":"
    print (modr n b)

    putStrLn $ "secuencia fibonacci en la iteración " ++ show n ++ ":"
    print (fibonacci n)
