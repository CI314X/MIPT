import random
import matplotlib.pyplot as plt

class GeneticAlgorithm:
    """
    Генетический алгоритм для нахождения минимума фукнции
    gamma - для арифметического кроссовера
    break_cond -  максимум из популяции - 0
                  среднее квадртичное   - 1
    """
    def __init__(self, x_min, x_max, y_min, y_max, test_function, size=40, selection_threshold=0.7,
                 crossbreeding_chance=0.7, gamma=0.3, mutation_chance=0.1, break_cond=0):
        self.x_min, self.x_max, self.y_min, self.y_max = x_min, x_max, y_min, y_max
        self.size = size
        self.function = test_function
        self.population = []
        self.selection_threshold, self.crossbreeding_chance = selection_threshold, crossbreeding_chance
        self.gamma, self.mutation_chance = gamma, mutation_chance
        self.new_population = []
        self.min = [0., 0.]
        self.break_cond = break_cond

    def _adaptation_function(self, x):
        """ Фукнция приспособления """
        # return np.exp(self.function(x))
        return self.function(x)

    def _initial_population(self):
        """ Инициализация начальной популяции"""
        random.seed(version=2)
        self.population = []
        for i in range(self.size):
            self.population.append([random.uniform(self.x_min, self.x_max), random.uniform(self.y_min, self.y_max)])
        return self.population

    def _selection(self):
        """ Селекция усечением для получения родителей """
        self.population.sort(key=lambda x: self._adaptation_function(x))
        self.population = self.population[:int(self.size * self.selection_threshold)]

    def _arithmetic_crossover(self, parent1, parent2):
        child1 = [self.gamma * parent1[0] + (1 - self.gamma) * parent2[0],
                  self.gamma * parent1[1] + (1 - self.gamma) * parent2[1]]
        child2 = [self.gamma * parent2[0] + (1 - self.gamma) * parent1[0],
                  self.gamma * parent2[1] + (1 - self.gamma) * parent1[1]]
        return child1, child2

    def _crossbreeding(self):
        """ Скрещивание.Рождаем детей """
        random.seed(version=2)
        size = len(self.population)
        k = 0
        children = []
        while k < size:
            i, j = random.randint(0, size - 1), random.randint(0, size - 1)
            if self.crossbreeding_chance > random.uniform(0, 1):
                ch1, ch2 = self._arithmetic_crossover(self.population[i], self.population[j])
                children.append(ch1)
                children.append(ch2)
                k += 2
        return children

    def _new_generation(self, children):
        """ Отбор новой популяции """
        size = len(self.population)
        new_p = self.population + children
        new_p.sort(key=lambda x: self._adaptation_function(x))
        self.new_population = new_p[:size]

    def _mutation(self):
        """
        Мутация всей новой популяции
        Вероятность мутации можно взять например 1/len(population). В этом случае каждая
        хромосома мутирует в среднем один раз
        """
        random.seed()
        for individual in self.new_population:
            if self.mutation_chance > random.uniform(0, 1):
                individual[0] = random.uniform(self.x_min, self.x_max)
            if self.mutation_chance > random.uniform(0, 1):
                individual[1] = random.uniform(self.y_min, self.y_max)

    def _break_condition(self, population):
        """ Критерий остановки поиска """
        if self.break_cond == 0:
            return max(list(map(lambda x: self._adaptation_function(x), population)))
        if self.break_cond == 1:
            return (sum(list(map(lambda x: self._adaptation_function(x)**2, population)))/len(population))**0.5

    def fit(self, n_iter=0, eps0=1e-3):
        self.population = self._initial_population()
        eps_old = self._break_condition(self.population)
        n = 0
        while True:
            self._selection()
            children = self._crossbreeding()
            self._new_generation(children)
            eps_new = self._break_condition(self.new_population)
            self.population = self.new_population
            n += 1
            x_a = [i[0] for i in self.population]
            y_a = [i[1] for i in self.population]
            self._mutation()
            if abs(eps_new - eps_old) < eps0 or (n_iter != 0 and n >= n_iter):
                print("Количество итераций: ", n)
                plt.xlim((self.x_min-1, self.x_max+1))
                plt.ylim((self.y_min-1, self.y_max+1))
                plt.scatter(x_a, y_a)
                plt.show()
                break
            eps_old = eps_new

    def min_value(self):
        """ Возвращает значение функции в точке экстремума """
        return self.function(self.arguments())

    def arguments(self):
        """ Возвращает координаты экстремума """
        self.population.sort(key=lambda x: self._adaptation_function(x))
        return self.population[0]
