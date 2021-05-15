from genetic_algorithm import GeneticAlgorithm
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np


def func(a):
    f = get_tf_hyperbolic_potential_abs(n=3, a=[0.5, 0.3, 1], c=[[0, 0], [1, -1], [-2, 1]],
                                        p=[[2.0, 1.3], [1.0, -1.0], [1.0, 1.2]], b=[3, -2, 2])

    return f(a)


def get_tf_hyperbolic_potential_abs(n: int, a, c, p, b):
    """
    :param n: количество экстремумов
    :param a: коэффициенты, определяющие крутость функции в районе экстремума list[float]
    :param c: список координат экстремумов                      list[list[float]
    :param p: степени гладкости функции в районе экстремума       list[list[float]]
    :param b: список коэффициентов, определяющих значения функции в точках экстремумов  list[float]
    """

    def ret_f(x):
        value = 0
        for i in range(n):
            res = 0
            for j in range(len(x)):
                res = res + np.abs(x[j] - c[i][j]) ** p[i][j]
            res = a[i] * res + b[i]
            res = -(1 / res)
            value = value + res
        return value

    return ret_f


def test_function1(a):
    x, y = a[0], a[1]
    return np.sin(x)


def test_function2(a):
    """ f(1;0,5) = 4 """
    x, y = a[0], a[1]
    return x**3+8*y**3-6*x*y+5


def test_function3(a):
    """   f(3;0,5) = 0 """
    x, y = a[0], a[1]
    return (1.5-x+x*y)**2 + (2.25-x+x*y**2)**2 + (2.625-x+x*y**3)**2


def test_function4(a):
    """   f(1;3) = 0 """
    x, y = a[0], a[1]
    return (x+2*y-7)**2 + (2*x+y-5)**2


x_min, x_max = -50.0, 50
y_min, y_max = -50.0, 50
gena = GeneticAlgorithm(x_min, x_max, y_min, y_max, test_function1, size=100, selection_threshold=0.7,
                        crossbreeding_chance=0.7, gamma=0.2, mutation_chance=0.1, break_cond=0)
gena.fit(n_iter=1e3, eps0=1e-2)
arg = gena.arguments()
print("Значение функции в точке минимума = {:f}".format(gena.min_value()))
print("(x, y) = ({:.2f}, {:.2f})".format(arg[0], arg[1]))

graph = 0
if graph == 1:
    X, Y = np.meshgrid(np.linspace(x_min, x_max, 50), np.linspace(y_min, y_max, 50))
    Z = np.zeros_like(X)
    for i in range(X.shape[0]):
        for j in range(Y.shape[0]):
            Z[i][j] = test_function1([X[i][j], Y[i][j]])
    fig = plt.figure(figsize=(10, 6))
    axes = Axes3D(fig)
    axes.set_xlabel('X')
    axes.set_ylabel('Y')
    axes.set_zlabel('F(x,y)')
    axes.plot_surface(X, Y, Z)
    plt.show()
