/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> 
#include "traits.hpp"
#include "isop.hpp"



namespace kitty {

    /*! \brief Threshold logic function identification

    Given a truth table, this function determines whether it is a threshold logic function (TF)
    and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

    f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

    where w_i are the weight values and T is the threshold value.
    The linear form of a TF is the vector [w_1, ..., w_n; T].

    \param tt The truth table
    \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
               The linear form has `tt.num_vars()` weight values and the threshold value
               in the end.
    \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
    */

    template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
    bool is_threshold(const TT& tt, std::vector<int64_t>* plf = nullptr)
    {
        uint64_t num_var = tt.num_vars();   //Number of variables in our truth table
        std::vector<int64_t> linear_form(num_var + 1);
        std::vector<bool> flipped_vars(num_var);    //Stores the information of which variables are flipped
        auto tt_fl = tt;    //Copy of tt where some variables will be flipped

        //Check if the function is positive or negative unate and flip the negative unate variables
        for (uint8_t var_index = 0; var_index < num_var; var_index++) {
            if (implies(cofactor0(tt, var_index), cofactor1(tt, var_index))) {
                flipped_vars.at(var_index) = false;
            }
            else if (implies(cofactor1(tt, var_index), cofactor0(tt, var_index))) {
                flip_inplace(tt_fl, var_index);
                flipped_vars.at(var_index) = true; //The variable has been flipped 
            }
            else {
                //the function is binate in this variable
                return false;
            }
        }

        //Inizialize the ILP solver
        lprec* lp;
        int *colno = NULL;
        REAL *row = NULL;
        lp = make_lp(0, num_var + 1);
        for (int i = 1; i <= (int) num_var + 1; i++) { 
            //Mark all variables as integer numbers
            set_int(lp, i, TRUE);
        }
        colno = (int *) malloc((num_var + 1) * sizeof(*colno));
        row = (REAL *) malloc((num_var + 1) * sizeof(*row));

        set_add_rowmode(lp, TRUE); //The constraints are added row by row

        //Compute the cubes of the onset
        std::vector<cube> onset_isop = isop(tt_fl);
        for (auto& current_cube : onset_isop) { //for every cube

            for (uint8_t var_index = 0; var_index < num_var; var_index++) { //for every literal

                auto current_cube_without_literal = current_cube;
                current_cube_without_literal.remove_literal(var_index);

                //Add the constraint to the ILP solver
                if (current_cube.num_literals() != current_cube_without_literal.num_literals()) {
                    //the cube contains the literal
                    colno[var_index] = var_index + 1;
                    row[var_index] = 1;
                }
                else {
                    //the cube does not contain the literal --> not in the equation so coefficient zero
                    colno[var_index] = var_index + 1;
                    row[var_index] = 0;
                }
            }
            colno[num_var] = num_var + 1; //Add the constraint for T
            row[num_var] = -1;            //
            add_constraintex(lp, num_var + 1, row, colno, GE, 0);
        }
        
        //Compute the cubes of the offset
        std::vector<cube> offset_isop = isop(unary_not(tt_fl));
        for (auto& current_cube : offset_isop) { //for every cube
            
            for (uint8_t var_index = 0; var_index < num_var; var_index++) { //for every literal

                auto current_cube_without_literal = current_cube;
                current_cube_without_literal.remove_literal(var_index);

                //Add the constraint to the ILP solver
                if (current_cube.num_literals() == current_cube_without_literal.num_literals()) {
                    //The offset cube does not contain the literal --> add it to the equation
                    colno[var_index] = var_index + 1;
                    row[var_index] = 1;
                }
                else {
                    //The offset cube contains the literal --> not in the equation, coefficient zero
                    colno[var_index] = var_index + 1;
                    row[var_index] = 0;
                }
            }
            colno[num_var] = num_var + 1; //Add the constraint for T
            row[num_var] = -1;            //
            add_constraintex(lp, num_var + 1, row, colno, LE, -1);
        }
        
        //Add the constraint that every variable must be greater than zero
        for (uint8_t i = 0; i < num_var + 1; i++) {
            for (uint8_t j = 0; j < num_var + 1; j++) {
                colno[j] = j + 1;
                row[j] = (i == j) ? 1 : 0;
            }
            add_constraintex(lp, num_var + 1, row, colno, GE, 0);
        }

        set_add_rowmode(lp, FALSE); //Rowmode should be turned off again when done building the model
        
        //Set the objective function
        for (uint8_t var_index = 0; var_index < num_var + 1; var_index++) {
            colno[var_index] = var_index + 1;
            row[var_index] = 1;
        }
        set_obj_fnex(lp, num_var + 1, row, colno);

        //Solve the ILP problem
        set_verbose(lp, IMPORTANT);
        set_minim(lp);
        int result = solve(lp);
        get_variables(lp, row);

        //Save the linear form 
        for(uint8_t var_index = 0; var_index < num_var; var_index++) {
            linear_form[var_index] = (flipped_vars[var_index]) ? -row[var_index] : row[var_index];
            row[num_var] = (flipped_vars[var_index]) ? row[num_var] - row[var_index] : row[num_var];
        }
        linear_form[num_var] = (row[num_var]);
        
        //Free allocated memory
        if(row != NULL)
            free(row);
        if(colno != NULL)
            free(colno);
        if(lp != NULL) 
            delete_lp(lp);

        //Return the results
        if(result == 0) {
            if(plf)
                *plf = linear_form;
            return true;
        }
        else {
            return false;
        }
    }
    
} /* namespace kitty */