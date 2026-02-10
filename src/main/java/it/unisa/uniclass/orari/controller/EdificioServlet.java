package it.unisa.uniclass.orari.controller;

import it.unisa.uniclass.orari.model.Aula;
import it.unisa.uniclass.orari.service.AulaService;
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;
import java.util.List;

@WebServlet(name = "EdificioServlet", value = "/EdificioServlet")
public class EdificioServlet extends HttpServlet {

    // Injection gestita dal container: il service avrà i suoi DAO pronti
    @EJB
    private AulaService aulaService;

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            String edificio = req.getParameter("ed");
            List<Aula> aule = aulaService.trovaAuleEdificio(edificio);

            req.setAttribute("aule", aule);
            req.setAttribute("ed", edificio);
            req.getRequestDispatcher("/edificio.jsp").forward(req, resp);
        } catch (Exception e) {
            req.getServletContext().log("Error processing edificio request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR, "An error occurred processing your request");
            } catch (IOException ioException) {
                req.getServletContext().log("Failed to send error response", ioException);
            }
        }
    }

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        doGet(req, resp);
    }
}