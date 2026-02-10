package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.service.dao.AulaRemote;
import jakarta.ejb.EJB;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.List;

@WebServlet("/AulaServlet")
public class AulaServlet extends HttpServlet {
    @EJB
    private AulaRemote aulaDao;

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        List<String> edificitotali = aulaDao.trovaEdifici();
        request.setAttribute("edificitotali", edificitotali);

        RequestDispatcher dispatcher = request.getRequestDispatcher("aula.jsp");
        dispatcher.forward(request, response);
    }
}
