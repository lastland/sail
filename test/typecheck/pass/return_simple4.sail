val return_test : forall 'n 'm, 10 <= 'm <= 'n. atom('m) -> {'m, 10 <= 'm <= 'n. atom('m)}

function return_test x = return(x)
