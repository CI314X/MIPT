#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <string.h>

static const double alpha = 0.2; // ширина ПСУ относительно длины отрезка
static const double kappa = 1.4;
static double R = 287.;
static double Pr = 0.72;
// Задание граничных условий
static double rho1 = 1.2; // плотность слева



//модель TCL обменного члена Пij
int tcl(double* Pxx, double* u, double* Rxx, double* Rtt, int N, double h)
{
    double k_energy;
    double axx; // тензор анизотропии напряжений Рейнольдса
    for (int i = 2; i < N; ++i)
    {
        k_energy = 0.5 * Rxx[i] + Rtt[i];
        axx = (Rxx[i] - 2. / 3 * k_energy) / k_energy;
        Pxx[i] = (u[i + 1] - u[i - 1]) / 2 / h * (k_energy * 8. / 15 + 0.6 * k_energy * (2. / 3 * axx + Rxx[i] / k_energy * axx  - axx * axx ) );

    }
    int i = N;
    k_energy = 0.5 * Rxx[i] + Rtt[i];
    axx = (Rxx[i] - 2. / 3 * k_energy) / k_energy;
    Pxx[i] = (u[i] - u[i - 1]) / h * (k_energy * 8. / 15 + 0.6 * k_energy * (2. / 3 * axx + Rxx[i] / k_energy * axx  - axx * axx ));

    return 0;
}

//копирование массива A в массив B
int arr_copy(double* A, double* B, int N)
{
    for (int i = 0; i < N; ++i)
    {
        B[i] = A[i];
    }
    return 0;
}

// для TVD схемы
//beta = 1 (MINMOD)
double limited_slope(double beta, double delta_l, double delta_r)
{
    if (delta_r > 0)
    {
        double tmp = fmax(0., fmin(beta * delta_l, delta_r));
        return fmax(tmp, fmin(delta_l, beta * delta_r));
    }
    else
    {
        double tmp = fmin(0., fmax(beta * delta_l, delta_r));
        return fmin(tmp, fmax(delta_l, beta * delta_r));
    }
}


//заполнение среднего поля скорости, 5% от всего промежутка - длина ПСУ, линейное распределение
int fill_u(double* u, double* p, double* rho,double* T, int N, double h, double x0, double M, double c_speed)
{
    double u1 = M * c_speed; // скорость слева от скачка
    double u2 = u1 * (1. - 2. / (kappa + 1) / M / M * (M * M - 1)); // скорость справа от скачка
    double p1 = c_speed * c_speed / kappa * rho1;
    double p2 = p1 * (1 + 2 * kappa / (kappa + 1) * (M * M - 1)); // давление справа от скачка

    double rho2 = rho1 * u1 / u2; // плотность справа от ПСУ
    printf("fill_u:  u1 = %f, u2 = %f\n", u1, u2);
    printf("fill_u:  p1 = %f, p2 = %f\n", p1, p2);
    printf("fill_u:  rho1 = %f, rho2 = %f\n", rho1, rho2);
    int left = (int)N / 2 - (int)(N * alpha / 2 - 1); // левый конец ПСУ
    int right = (int)N / 2 + (int)(N * alpha / 2); // правый конец ПСУ
    printf("fill_u:  left = %d, right = %d\n", left, right);
    printf("H shock = %f\n", (right-left+1)*h);
    //y = kx+b
    double k_u = (u1 - u2) / (left * h - right * h); // =(u1-u2)/(x1-x2)
    double b_u = u1 - k_u * (x0 + left * h);

    double k_p = (p1 - p2) / (left * h - right * h);
    double b_p = p1 - k_p * (x0 + left * h);

    double k_r = (rho1 - rho2) / (left * h - right * h);
    double b_r = rho1 - k_r * (x0 + left * h);

    for (int i = 0; i < N + 1; ++i)
    {
        if (i < left)
        {
            u[i] = u1;
            p[i] = p1;
            rho[i] = rho1;
            T[i] = p[i] / R / rho[i];
        }
        else if (i > right)
        {
            u[i] = u2;
            p[i] = p2;
            rho[i] = rho2;
            T[i] = p[i] / R / rho[i];
        }
        else
        {
            u[i] = k_u * (x0 + i * h) + b_u;
            p[i] = k_p * (x0 + i * h) + b_p;
            rho[i] = k_r * (x0 + i * h) + b_r;
            T[i] = p[i] / R / rho[i];
        }
    }
    return 0;
}


//заполнение среднего поля скорости, 5% от всего промежутка - длина ПСУ, линейное распределение
// задание ступеньки
int fill_uuu(double* u, double* p, double* rho,double* T, int N, double h, double x0, double M, double c_speed)
{
    double p1 = c_speed * c_speed / kappa * rho1;
    double u1 = M * c_speed; // скорость слева от скачка
    double u2 = u1 * (1. - 2. / (kappa + 1) / M / M * (M * M - 1)); // скорость справа от скачка

    double p2 = p1 * (1 + 2 * kappa / (kappa + 1) * (M * M - 1)); // давление справа от скачка

    double rho2 = rho1 * u1 / u2; // плотность справа от ПСУ
    printf("fill_u:  u1 = %f, u2 = %f\n", u1, u2);
    printf("fill_u:  p1 = %f, p2 = %f\n", p1, p2);
    printf("fill_u:  rho1 = %f, rho2 = %f\n", rho1, rho2);
    int left = (int)N / 2;
    //y = kx+b

    for (int i = 0; i < N + 1; ++i)
    {
        if (i < left)
        {
            u[i] = u1;
            p[i] = p1;
            rho[i] = rho1;
            T[i] = p[i] / R / rho[i];
        }
        else
        {
            u[i] = u2;
            p[i] = p2;
            rho[i] = rho2;
            T[i] = p[i] / R / rho[i];
        }

    }
    return 0;
}

int main()
{
    //printf("Mt=0.12;M=1.2\n");
    int rc = 0; // ошибка

    char name1[] = "M=1.1_Mt=0.05_1500.txt"; // имя файла
    //char name2[] = "tvd_no_lim_800_delta.txt"; // имя файла
    //printf("Name file = %s\n", name);

    const int N = 1500; // число узлов N+1 ( [0-N] )    500
    const double h = 1e-6; // шаг по x                 2e-5
    double eps = 1e-4; // критерий выхода
    double x0 = 0.0; // начальная координата
    double dt; // шаг по времени

    int max_steps = 1e8; // максимальное количество итераций

    double* u; // поле скорости
    double* p; // поле давления
    double* rho; // поле давления
    double* T; // поле температуры
    u = (double*)calloc(N+1, sizeof(double));
    p = (double*)calloc(N+1, sizeof(double));
    rho = (double*)calloc(N+1, sizeof(double));
    T = (double*)calloc(N+1, sizeof(double));

    double M = 1.1; // число Маха
    double c_speed = 341.0; //скорость звука
    double M_turb = 0.05; // турбулентное число Маха
    double k = 0.5 * M_turb * M_turb * c_speed * c_speed; //константа для задания кинетической энергии турб. (2/3k)

    // константы для модели TCL
    double C_PD = 0.4; //0.4
    double c1_div = 4.0; //4.0

    //Константы
    double Cp = kappa/(kappa - 1.) * R;
    double Cv = 1. / (kappa - 1.) * R;
    double p1 = c_speed * c_speed / kappa * rho1;
    double u1 = M * c_speed; // скорость слева от скачка
    double u2 = u1 * (1. - 2. / (kappa + 1) / M / M * (M * M - 1)); // скорость справа от скачка
    double p2 = p1 * (1 + 2 * kappa / (kappa + 1) * (M * M - 1)); // давление справа от скачка
    double rho2 = rho1 * u1 / u2; // плотность справа от ПСУ

    double Cu = 0.02; // число Куранта(множитель для шага dt)

    double* nu_turb = (double*)calloc(N, sizeof(double)); // т-тная вязкость, вычисляемая на гранях ячеек

    double C_turb = 6.; // константа для турб-ой вязкости
    //double alpha_turb = 0.;
    double beta_turb = 1.;
    double gamma_turb = 3.;
    double M0_turb = 1e-8;


    double L_turb = 1e-3; // интегральный масштаб турбулетности
    double h_shock = 0.05; // для измерения толщины ПСУ (задать в процентах относительно изменени параметров)


    dt = h / (u1 + pow(kappa * p2 / rho2, 0.5)) * Cu; // выбираем шаг по времени // конвективный шаг по времени
    // dt = 0.25 * h * h / nu_turb; // диффузионный шаг по времени
    rc = fill_u(u, p, rho, T, N, h, x0, M, c_speed); // Заполняем поля скорости, давления, плотности
    printf("dt = %.13f\n", dt);
    //считаем H скачка
    int left = -1; int right = -1;
    int l_2 = -1; int r_2 = -1;
    double du = h_shock * (u[0] - u[N]);
    for (int i = 0; i < N + 1; ++i)
    {
        if( fabs(u[i]-u[0]) / u[0] > h_shock && left == -1) left = i;
        if( fabs(u[i]-u[N]) / u[N] < h_shock && right == -1) right = i;
        if( (u[i] < (u[0] - du)) && l_2 == -1) l_2 = i;

    }
    for (int i = N; i > 0; --i)
    {
        if( (u[i] > (u[N] + du)) && r_2 == -1) r_2 = i;
    }
    printf("Before: left = %d, right = %d\n", left, right);
    printf("Before: H shock = %f\n", (right-left+1)*h);
    printf("left = %d; right = %d\n",l_2,r_2);
    printf("New. Before: H shock = %f\n", (r_2-l_2+1)*h);

    double* Rxx, * Rxx_new;    // напряжения Рейнольдса
    double* Rtt, * Rtt_new;    // напряжения Рейнольдса (Ryy=Rzz)
    double* Pxx; // обменный член
    Rxx = (double*)calloc(N+1, sizeof(double));
    Rxx_new = (double*)calloc(N+1, sizeof(double));
    Rtt = (double*)calloc(N+1, sizeof(double));
    Rtt_new = (double*)calloc(N+1, sizeof(double));
    Pxx = (double*)calloc(N+1, sizeof(double));
    for (int i = 0; i < N + 1; ++i) // задание напряжений Рейнольдса
    {
        Rxx[i] = 2. / 3. * k;
        Rtt[i] = 2. / 3. * k;
    }
    rc = arr_copy(Rxx, Rxx_new, N + 1);
    rc = arr_copy(Rtt, Rtt_new, N + 1);


    //Создание консервативных переменных
    // a1 = rho
    // a2 = rho*u
    // a3 = rho * E
    double* a1 = (double*)calloc(N+1, sizeof(double));
    double* a2 = (double*)calloc(N+1, sizeof(double));
    double* a3 = (double*)calloc(N+1, sizeof(double));
    double* a1_new = (double*)calloc(N+1, sizeof(double));
    double* a2_new = (double*)calloc(N+1, sizeof(double));
    double* a3_new = (double*)calloc(N+1, sizeof(double));

    // Создание потоков
    double* F_rho;
    double* F_rho_u;
    double* F_rho_E;
    F_rho = (double*)calloc(N, sizeof(double));
    F_rho_u = (double*)calloc(N, sizeof(double));
    F_rho_E = (double*)calloc(N, sizeof(double));

    // метод Роу
    double* u_tilde = (double*)calloc(N, sizeof(double));
    double* H_tilde = (double*)calloc(N, sizeof(double));
    double* a_tilde = (double*)calloc(N, sizeof(double));

    double* alpha1 = (double*)calloc(N, sizeof(double));
    double* alpha2 = (double*)calloc(N, sizeof(double));
    double* alpha3 = (double*)calloc(N, sizeof(double));

    double* lambda1 = (double*)calloc(N, sizeof(double));
    double* lambda2 = (double*)calloc(N, sizeof(double));
    double* lambda3 = (double*)calloc(N, sizeof(double));

    // TVD схема
    double beta = 1.; // 1 - MINMOD, 2 - SUPERBEE
    //double* tvd_delta = (double*)calloc(N, sizeof(double));
    double* a1_L_tvd = (double*)calloc(N, sizeof(double)); // rho
    double* a1_R_tvd = (double*)calloc(N, sizeof(double));
    double* a2_L_tvd = (double*)calloc(N, sizeof(double)); // rho*u
    double* a2_R_tvd = (double*)calloc(N, sizeof(double));
    double* a3_L_tvd = (double*)calloc(N, sizeof(double)); // rho*E
    double* a3_R_tvd = (double*)calloc(N, sizeof(double));
    // левые и правые значения для потоков
    double* rho_l = (double*)calloc(N, sizeof(double));
    double* rho_r = (double*)calloc(N, sizeof(double));
    double* u_l = (double*)calloc(N, sizeof(double));
    double* u_r = (double*)calloc(N, sizeof(double));
    double* p_l = (double*)calloc(N, sizeof(double));
    double* p_r = (double*)calloc(N, sizeof(double));
    double* T_l = (double*)calloc(N, sizeof(double));
    double* T_r = (double*)calloc(N, sizeof(double));

    double* delta_a1 = (double*)calloc(N+1, sizeof(double));
    double* delta_a2 = (double*)calloc(N+1, sizeof(double));
    double* delta_a3 = (double*)calloc(N+1, sizeof(double));

    // величины с чертой сверху
    double* a1_L_tvd_line = (double*)calloc(N, sizeof(double));
    double* a1_R_tvd_line = (double*)calloc(N, sizeof(double));
    double* a2_L_tvd_line = (double*)calloc(N, sizeof(double));
    double* a2_R_tvd_line = (double*)calloc(N, sizeof(double));
    double* a3_L_tvd_line = (double*)calloc(N, sizeof(double));
    double* a3_R_tvd_line = (double*)calloc(N, sizeof(double));

    int steps = 0; //счетчик шагов
    int num_file = 0; // счетчик файлов
    double eps0, eps1; //  eps на каждом шаге алгоритма

    do
    {
        //вывод в файл
        //        if (steps % 100000 == 0) {
        //            FILE* fpp;
        //            double x;
        //            char str_n[80];
        //            rc = sprintf (str_n, "fields %d.txt", num_file);
        //            printf("%s\n",str_n);
        //            rc = fopen_s(&fpp, str_n, "w+");
        //            fprintf(fpp, "i x u p rho T nu_turb Rxx Rtt k/k0 Rxx/Rtt\n");
        //            double k_energy; // кинетическая энергия турбулентности
        //            double k0_energy = 0.5 * Rxx[0] + Rtt[0];
        //            double axx; // тензор анизотропии
        //            for (int i = 0; i < N + 1; ++i)
        //            {
        //                x = x0 + i * h;
        //                k_energy = 0.5 * Rxx[i] + Rtt[i];
        //                axx = (Rxx[i] - 2. / 3 * k_energy) / k_energy;
        //                fprintf(fpp, "%d %.8f %.8f %.8f %.8f %.8f %.8f %.8f %.8f %.8f %.8f\n", i, x, u[i], p[i], rho[i], T[i], nu_turb[i], Rxx[i], Rtt[i], k_energy/k0_energy,  Rxx[i]/Rtt[i]);
        //            }
        //            fclose(fpp);
        //            num_file += 1;
        //        }

        // 1 ЧАСТЬ

        // Пересчет в консервативные
        for (int i = 0; i < N + 1; ++i)
        {
            T[i] = p[i] / R / rho[i];
            a1[i] = rho[i];
            a2[i] = rho[i] * u[i];
            a3[i] = rho[i] * (u[i] * u[i] / 2. + Cv * T[i]);
        }
        rc = arr_copy(a1, a1_new, N + 1);
        rc = arr_copy(a2, a2_new, N + 1);
        rc = arr_copy(a3, a3_new, N + 1);

        // TVD схема (повышение порядка)
        for (int i = 0; i < N + 1; ++i)
        {
            double delta_l_rho, delta_r_rho, delta_l_rho_u, delta_r_rho_u, delta_l_rho_E, delta_r_rho_E;
            if (i == 0) // в самой левой точке
            {
                delta_l_rho = 0.;
                delta_r_rho = a1[1] - a1[0];
                delta_l_rho_u = 0.;
                delta_r_rho_u = a2[1] - a2[0];
                delta_l_rho_E = 0.;
                delta_r_rho_E = a3[1] - a3[0];
            }
            else if (i == N) // в самой правой точке
            {
                delta_l_rho = a1[i] - a1[i-1];
                delta_r_rho = 0.;
                delta_l_rho_u = a2[i] - a2[i-1];
                delta_r_rho_u = 0.;
                delta_l_rho_E = a3[i] - a3[i-1];
                delta_r_rho_E = 0.;
            }
            else
            {
                delta_l_rho = a1[i] - a1[i-1];
                delta_r_rho = a1[i+1] - a1[i];
                delta_l_rho_u = a2[i] - a2[i-1];
                delta_r_rho_u = a2[i+1] - a2[i];
                delta_l_rho_E = a3[i] - a3[i-1];
                delta_r_rho_E = a3[i+1] - a3[i];
            }
            //            // delta с полоской
            //            delta_a1[i] = limited_slope(beta, delta_l_rho, delta_r_rho);
            //            delta_a2[i] = limited_slope(beta, delta_l_rho_u, delta_r_rho_u);
            //            delta_a3[i] = limited_slope(beta, delta_l_rho_E, delta_r_rho_E);

            // обычная delta
            delta_a1[i] = 0.5 * (delta_l_rho + delta_r_rho);
            delta_a2[i] = 0.5 * (delta_l_rho_u + delta_r_rho_u);
            delta_a3[i] = 0.5 * (delta_l_rho_E + delta_r_rho_E);
        }
        // Значения L и R для i-го потока
        for (int i = 0; i < N; ++i)
        {
            a1_L_tvd[i] = a1[i] + 0.5 * delta_a1[i]; // L для i-го потока
            a1_R_tvd[i] = a1[i+1] - 0.5 * delta_a1[i+1];
            a2_L_tvd[i] = a2[i] + 0.5 * delta_a2[i];
            a2_R_tvd[i] = a2[i+1] - 0.5 * delta_a2[i+1];
            a3_L_tvd[i] = a3[i] + 0.5 * delta_a3[i];
            a3_R_tvd[i] = a3[i+1] - 0.5 * delta_a3[i+1];

            // считаем величины с полосками
            a1_L_tvd_line[i] = a1_L_tvd[i] + 0.5 * dt / h * (a2_L_tvd[i] - a2_R_tvd[i]);
            a1_R_tvd_line[i] = a1_R_tvd[i] + 0.5 * dt / h * (a2_L_tvd[i] - a2_R_tvd[i]);
            a2_L_tvd_line[i] = a2_L_tvd[i] + 0.5 * dt / h * (a2_L_tvd[i] * a2_L_tvd[i] / a1_L_tvd[i] + (a3_L_tvd[i] - a2_L_tvd[i] * a2_L_tvd[i] / 2. / a1_L_tvd[i]) * R / Cv - \
                                                             (a2_R_tvd[i] * a2_R_tvd[i] / a1_R_tvd[i] + (a3_R_tvd[i] - a2_R_tvd[i] * a2_R_tvd[i] / 2. / a1_R_tvd[i]) * R / Cv) );
            a2_R_tvd_line[i] = a2_R_tvd[i] + 0.5 * dt / h * (a2_L_tvd[i] * a2_L_tvd[i] / a1_L_tvd[i] + (a3_L_tvd[i] - pow(a2_L_tvd[i], 2.) / 2. / a1_L_tvd[i]) * R / Cv - \
                                                             (a2_R_tvd[i] * a2_R_tvd[i] / a1_R_tvd[i] + (a3_R_tvd[i] - pow(a2_R_tvd[i], 2.) / 2. / a1_R_tvd[i]) * R / Cv) );
            a3_L_tvd_line[i] = a3_L_tvd[i] + 0.5 * dt / h * ((a3_L_tvd[i] - pow(a2_L_tvd[i], 2.) / 2. / a1_L_tvd[i]) * R / Cv * a2_L_tvd[i] / a1_L_tvd[i] + \
                                                             a2_L_tvd[i] / a1_L_tvd[i] * a3_L_tvd[i] - \
                                                             ((a3_R_tvd[i] - pow(a2_R_tvd[i], 2.) / 2. / a1_R_tvd[i]) * R / Cv * a2_R_tvd[i] / a1_R_tvd[i] + \
                                                              a2_R_tvd[i] / a1_R_tvd[i] * a3_R_tvd[i]) );
            a3_R_tvd_line[i] = a3_R_tvd[i] + 0.5 * dt / h * ((a3_L_tvd[i] - pow(a2_L_tvd[i], 2.) / 2. / a1_L_tvd[i]) * R / Cv * a2_L_tvd[i] / a1_L_tvd[i] + \
                                                             a2_L_tvd[i] / a1_L_tvd[i] * a3_L_tvd[i] - \
                                                             ((a3_R_tvd[i] - pow(a2_R_tvd[i], 2.) / 2. / a1_R_tvd[i]) * R / Cv * a2_R_tvd[i] / a1_R_tvd[i] + \
                                                              a2_R_tvd[i] / a1_R_tvd[i] * a3_R_tvd[i]) );
        }
        rc = arr_copy(a1_L_tvd_line, a1_L_tvd, N);
        rc = arr_copy(a1_R_tvd_line, a1_R_tvd, N);
        rc = arr_copy(a2_L_tvd_line, a2_L_tvd, N);
        rc = arr_copy(a2_R_tvd_line, a2_R_tvd, N);
        rc = arr_copy(a3_L_tvd_line, a3_L_tvd, N);
        rc = arr_copy(a3_R_tvd_line, a3_R_tvd, N);

        // i - для i-го потока
        //Roe averaged values
        // пересчет в новые переменные
        // значения на границах ячеек (для потоков)
        for (int i = 0; i < N; ++i)
        {
            rho_l[i] = a1_L_tvd[i]; // a1[i+1]
            rho_r[i] = a1_R_tvd[i]; // a1[i]
            u_l[i] = a2_L_tvd[i] / a1_L_tvd[i]; //a2[i+1]/a1[i+1]
            u_r[i] = a2_R_tvd[i] / a1_R_tvd[i];
            p_l[i] = (a3_L_tvd[i] - a2_L_tvd[i] * a2_L_tvd[i] / 2. / a1_L_tvd[i]) * R / Cv;
            p_r[i] = (a3_R_tvd[i] - a2_R_tvd[i] * a2_R_tvd[i] / 2. / a1_R_tvd[i]) * R / Cv;
            T_l[i] = p_l[i] / R / rho_l[i];
            T_r[i] = p_r[i] / R / rho_r[i];
        }


        for (int i = 0; i < N; ++i)
        {
            u_tilde[i] = (pow(rho_l[i], 0.5) * u_l[i] + pow(rho_r[i], 0.5) * u_r[i]) / (pow(rho_l[i], 0.5) + pow(rho_r[i], 0.5));
            H_tilde[i] = (pow(rho_l[i], 0.5) * (0.5 * u_l[i] * u_l[i] + p_l[i] * kappa / rho_l[i] / (kappa-1)) + \
                          pow(rho_r[i], 0.5) * (0.5 * u_r[i] * u_r[i] + p_r[i] * kappa / rho_r[i] / (kappa-1))) / (pow(rho_l[i], 0.5) + pow(rho_r[i], 0.5));
            a_tilde[i] = pow((kappa-1) * (H_tilde[i] - 0.5 * u_tilde[i] * u_tilde[i]), 0.5);
        }
        //аlpha and lambda
        for (int i = 0; i < N; ++i)
        {
            double delta_u_1 = rho_r[i] - rho_l[i];
            double delta_u_2 = rho_r[i] * u_r[i] - rho_l[i]* u_l[i];
            double delta_u_3 = rho_r[i] * (0.5 * u_r[i] * u_r[i] + Cv * T_r[i]) - rho_l[i] * (0.5 * u_l[i] * u_l[i] + Cv * T_l[i]);

            alpha2[i] = (kappa - 1) / pow(a_tilde[i], 2.0) * (delta_u_1 * (H_tilde[i] - pow(u_tilde[i], 2.0)) + u_tilde[i] * delta_u_2 - delta_u_3);
            alpha1[i] = 0.5 / a_tilde[i] * (delta_u_1 * (u_tilde[i] + a_tilde[i]) - delta_u_2 - a_tilde[i] * alpha2[i]);
            alpha3[i] = delta_u_1 - alpha1[i] - alpha2[i];

            lambda1[i] = u_tilde[i] - a_tilde[i];
            lambda2[i] = u_tilde[i];
            lambda3[i] = u_tilde[i] + a_tilde[i];
        }
        //вычисление потоков
        for (int i = 0; i < N; ++i)
        {
            double cspeed = pow(kappa * R * (T[i] + T[i+1]) / 2. , 0.5);
            double Mp = pow(L_turb * R * fabs((T[i+1] - T[i]) / h), 0.5) / cspeed;
            double divV = fabs((u[i+1] - u[i]) / h);
            double k_energy = 0.5 * Rxx[i] + Rtt[i]; // кинетическая энергия турбулентности
            double Mt = pow(2. * k_energy, 0.5) / cspeed;
            nu_turb[i] = fmin(0.15, C_turb * L_turb * L_turb * divV * pow(Mt, gamma_turb) / pow(fmax(Mp, M0_turb), beta_turb));

            F_rho[i] = 0.5 * (rho_l[i] * u_l[i] + rho_r[i] * u_r[i]) - 0.5 * ( alpha1[i] * fabs(lambda1[i]) * 1 +  \
                                                                               alpha2[i] * fabs(lambda2[i]) * 1 + \
                                                                               alpha3[i] * fabs(lambda3[i]) * 1 );
            F_rho_u[i] = 0.5 * (rho_l[i] * u_l[i] * u_l[i] + p_l[i] + rho_r[i] * u_r[i] * u_r[i] + p_r[i]) \
                    - 0.5 * ( alpha1[i] * fabs(lambda1[i]) * (u_tilde[i] - a_tilde[i]) +\
                              alpha2[i] * fabs(lambda2[i]) * u_tilde[i] + \
                              alpha3[i] * fabs(lambda3[i]) * (u_tilde[i] + a_tilde[i]) )\
                    - 4. / 3. * (rho[i] + rho[i+1]) / 2. * nu_turb[i] * (u[i+1] - u[i]) / h;
            F_rho_E[i] = 0.5 * (rho_l[i] * (u_l[i] * u_l[i] / 2. + Cv * T_l[i]) * u_l[i] + u_l[i] * p_l[i] +\
                                rho_r[i] * (u_r[i] * u_r[i] / 2. + Cv * T_r[i]) * u_r[i] + u_r[i] * p_r[i]) -\
                    0.5 * ( alpha1[i] * fabs(lambda1[i]) *(H_tilde[i] - u_tilde[i] * a_tilde[i]) + \
                            alpha2[i] * fabs(lambda2[i]) * 0.5 * u_tilde[i] * u_tilde[i] +
                            alpha3[i] * fabs(lambda3[i]) * (H_tilde[i] + u_tilde[i] * a_tilde[i]) ) \
                    - 4. / 3. * (rho[i] + rho[i+1]) / 2. * nu_turb[i] * (u[i+1] - u[i]) / h * (u[i] + u[i+1]) / 2. - (rho[i] + rho[i+1]) / 2. * nu_turb[i] * Cp / Pr * (T[i+1] - T[i]) / h;
        }

        // вычисление параметров (шаг по времени)
        for (int i = 1; i < N; ++i)
        {
            a1_new[i] = a1[i] + dt / h * ( F_rho[i-1] - F_rho[i] );
            a2_new[i] = a2[i] + dt / h * ( F_rho_u[i-1] - F_rho_u[i] );
            a3_new[i] = a3[i] + dt / h * ( F_rho_E[i-1] - F_rho_E[i] );
        }

        //вычисляем критерий выхода
        eps0 = -1.;
        for (int i = 0; i < N + 1; ++i)
        {
            double eps_temp = fabs(a1_new[i] - a1[i]) + fabs(a2_new[i] - a2[i]) + fabs(a3_new[i] - a3[i]);
            if (eps_temp > eps0)
                eps0 = eps_temp;
        }
        rc = arr_copy(a1_new, a1, N + 1);
        rc = arr_copy(a2_new, a2, N + 1);
        rc = arr_copy(a3_new, a3, N + 1);

        // Пересчет в примитивы
        for (int i = 0; i < N + 1; ++i)
        {
            rho[i] = a1[i];
            u[i] = a2[i] / a1[i];
            p[i] = (a3[i] - a2[i] * a2[i] / 2. / a1[i]) * R / Cv;
            T[i] = p[i] / R / rho[i];
        }
        //граничные условия
        p[N] = p2;
        u[N] = u[N-1];
        rho[N] = rho[N-1];
        p[0] = p1;
        u[0] = u1;
        rho[0] = rho1;

        // 2 ЧАСТЬ
        rc = tcl(Pxx, u, Rxx, Rtt, N, h); // задание обменного члена
        for (int i = 2; i < N; ++i)
        {
            double k_energy = 0.5 * Rxx[i] + Rtt[i]; // кинетическая энергия турбулентности
            double axx = (Rxx[i] - 2. / 3 * k_energy) / k_energy;
            double calib_xx = (u[i + 1] - u[i - 1]) / 2. / h * (2./3.* C_PD * k_energy + c1_div * k * axx);
            double calib_yy = (u[i + 1] - u[i - 1]) / 2. / h * (2./3.* C_PD * k_energy - 0.5 * c1_div * k  * axx);
            Rxx_new[i] = Rxx[i] + dt * (-u[i] * (Rxx[i - 2] - 4. * Rxx[i - 1] + 3. * Rxx[i]) / 2. / h - 2. * Rxx[i] * (u[i + 1] - u[i - 1]) / 2. / h + Pxx[i] + calib_xx );
            Rtt_new[i] = Rtt[i] + dt * (-u[i] * (Rtt[i - 2] - 4. * Rtt[i - 1] + 3. * Rtt[i]) / 2. / h - 0.5 * Pxx[i] + calib_yy);
        }
        int i = N; // понижаем точность для градиента средней скорости (левый уголок)
        double k_energy= 0.5 * Rxx[i] + Rtt[i]; // кинетическая энергия турбулентности
        double axx = (Rxx[i] - 2. / 3 * k_energy) / k_energy;
        double calib_xx = (u[i] - u[i - 1]) / h * (2./3.* C_PD * k_energy + c1_div * k * axx);
        double calib_yy = (u[i] - u[i - 1]) / h * (2./3.* C_PD * k_energy - 0.5 * c1_div * k * axx);

        Rxx_new[i] = Rxx[i] + dt * (-u[i] * (Rxx[i - 2] - 4. * Rxx[i - 1] + 3. * Rxx[i]) / 2. / h - 2. * Rxx[i] * (u[i] - u[i - 1]) / h + Pxx[i] + calib_xx);
        Rtt_new[i] = Rtt[i] + dt * (-u[i] * (Rtt[i - 2] - 4. * Rtt[i - 1] + 3. * Rtt[i]) / 2. / h - 0.5 * Pxx[i] + calib_yy);
        //вычисляем критерий выхода
        eps1 = -1.;
        for (int i = 0; i < N + 1; ++i)
        {
            double eps_temp = fabs(Rxx_new[i] - Rxx[i]) + fabs(Rtt_new[i] - Rtt[i]);
            if (eps_temp > eps1) eps1 = eps_temp;
        }
        rc = arr_copy(Rxx_new, Rxx, N + 1);
        rc = arr_copy(Rtt_new, Rtt, N + 1);
        steps += 1;


        if (steps % 4000 == 0) { // контроль на каждом --- шаге
            printf("Steps = %d; eps = %.10f\n", steps, eps0);
            printf("nu_turb[300] = %.10f\n",nu_turb[400]);
        }

    } while (fabs(eps0) + fabs(eps1) >= eps && steps < max_steps); // выход
    printf("Eps = %.15f\n", fabs(eps0) + fabs(eps1));
    printf("Steps = %d\n", steps);
    printf("END of 1 PART\n");

    double x;
    //вывод в файл
    // i  x[i]  u[i]  p[i] rho[i] T[i] nu_turb[i] Rxx[i] Rtt[i] k[i] axx[i] Rxx[i]/Rtt[i]
    double k_energy; // кинетическая энергия турбулентности
    double k0_energy = 0.5 * Rxx[0] + Rtt[0];
    double axx; // тензор анизотропии
    FILE* fp;
    rc = fopen_s(&fp, name1, "w+");
    fprintf(fp, "i x u p rho T nu_turb Rxx Rtt k/k0 Rxx/Rtt\n");
    left = -1;
    right = -1;
    l_2 = -1;r_2 = -1;
    du = h_shock * (u[0] - u[N]);
    for (int i = 0; i < N + 1; ++i)
    {
        //считаем толщину ПСУ
        if( fabs(u[i]-u[0]) / u[0] > h_shock && left == -1) left = i;
        if( fabs(u[i]-u[N]) / u[N] < h_shock && right == -1) right = i;
        if( (u[i] < (u[0] - du)) && l_2 == -1) l_2 = i; // другой расчет h скачка
        x = x0 + i * h;
        k_energy = 0.5 * Rxx[i] + Rtt[i];
        axx = (Rxx[i] - 2. / 3 * k_energy) / k_energy;
        fprintf(fp, "%d %.8f %.8f %.8f %.8f %.8f %.8f %.8f %.8f %.8f %.8f\n", i, x, u[i], p[i], rho[i], T[i], nu_turb[i], Rxx[i], Rtt[i], k_energy/k0_energy,  Rxx[i]/Rtt[i]);
    }

    fprintf(fp,"\n%.5f",(right-left+1)*h / L_turb); // запись отношения h/Lt
    fclose(fp);

    for (int i = N; i > 0; --i)
    {
        if( (u[i] > (u[N] + du)) && r_2 == -1) r_2 = i;
    }

    free(u); free(p); free(rho); free(T);
    free(nu_turb); free(a1); free(a2); free(a3); free(a1_new); free(a2_new); free(a3_new);
    free(Rxx); free(Rtt); free(Rxx_new); free(Rtt_new); free(Pxx);
    printf("After: left = %d, right = %d\n", left, right);
    printf("After: H shock = %f\n", (right-left+1)*h);
    printf("New. After: H shock = %f\n", (r_2-l_2+1)*h);





    printf("1. h/Lt = %.5f\n", (right-left+1)*h / L_turb);
    printf("2. h/Lt = %.5f\n", (r_2-l_2+1)*h / L_turb);
    return 0;
}
