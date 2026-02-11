package it.unisa.uniclass.common;

import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService; // Import necessario
import jakarta.ejb.EJB; // Import necessario
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import java.util.List;

@WebServlet(name = "indexServlet", value = "/Home")
public class IndexServlet extends HttpServlet {

    // 1. INIETTA IL SERVICE
    @EJB
    private CorsoLaureaService corsoLaureaService;

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) {
        try {
            HttpSession session = request.getSession(false);

            Utente user = (session != null)
                    ? (Utente) session.getAttribute("currentSessionUser")
                    : null;

            if (user == null) {
                response.sendRedirect("Login.jsp");
                return;
            }

            // 2. RECUPERA I CORSI DAL DB
            List<CorsoLaurea> corsi = corsoLaureaService.trovaTutti(); //

            // 3. PASSA LA LISTA ALLA JSP
            request.setAttribute("corsi", corsi);

            request.getRequestDispatcher("index.jsp").forward(request, response);

        } catch (Exception e) {
            e.printStackTrace(); // Utile per vedere errori nel log
            try {
                response.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (Exception ignored) {}
        }
    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) {
        doGet(request, response);
    }
}