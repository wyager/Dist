# Dist

#### A Haskell library for probability distributions

This library provides a data structure and associated functions for
representing discrete probability distributions.

This library is optimized for very fast sampling. If ```n``` is the number of unique outcomes,
sampling from the distribution is ```O(log(n))``` worst case, and ```O(1)``` best case.

The average time complexity depends on the distribution. A more evenly distributed
distribution will be closer to ```O(log(n))```. A less evenly dsitributed distribution
will be closer to ```O(1)```.