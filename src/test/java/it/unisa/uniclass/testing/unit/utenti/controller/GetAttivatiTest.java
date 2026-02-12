package it.unisa.uniclass.testing.unit.utenti.controller;

import it.unisa.uniclass.utenti.controller.GetAttivati;
import it.unisa.uniclass.utenti.model.Accademico;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.json.JSONArray;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.MockitoAnnotations;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.*;

@DisplayName("Test per la servlet GetAttivati")
class GetAttivatiTest {

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    private TestableGetAttivati servlet;

    /**
     * Sottoclasse per accedere ai metodi protected della servlet
     */
    private static class TestableGetAttivati extends GetAttivati {
        public void callDoGet(HttpServletRequest request, HttpServletResponse response)
                throws ServletException, java.io.IOException {
            doGet(request, response);
        }

        public void callDoPost(HttpServletRequest request, HttpServletResponse response)
                throws ServletException, java.io.IOException {
            doPost(request, response);
        }
    }

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        servlet = new TestableGetAttivati();
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));
    }

    @Test
    @DisplayName("doGet restituisce JSON corretto con accademici attivati")
    void testDoGet_viaService() throws Exception {
        // Prepara dati di test
        Accademico acc1 = new Accademico();
        acc1.setEmail("mario.rossi@example.com");

        Accademico acc2 = new Accademico();
        acc2.setEmail("luigi.bianchi@example.com");

        List<Accademico> attivati = new ArrayList<>();
        attivati.add(acc1);
        attivati.add(acc2);

        // StringWriter per intercettare l'output della servlet
        StringWriter stringWriter = new StringWriter();
        PrintWriter writer = new PrintWriter(stringWriter);
        when(response.getWriter()).thenReturn(writer);

        // Mock della costruzione del servizio
        try (MockedConstruction<AccademicoService> mocked = mockConstruction(AccademicoService.class,
                (mock, context) -> {
                    when(mock.trovaAttivati(true)).thenReturn(attivati);
                })) {

            servlet.callDoGet(request, response);
        }

        writer.flush(); // assicura che tutto sia scritto

        // Verifica l'output JSON
        JSONArray jsonArray = new JSONArray(stringWriter.toString());
        assertEquals(2, jsonArray.length());
        assertEquals("mario.rossi@example.com", jsonArray.getJSONObject(0).getString("email"));
        assertEquals("luigi.bianchi@example.com", jsonArray.getJSONObject(1).getString("email"));
    }

    @Test
    @DisplayName("doPost chiama super.doPost senza errori")
    void testDoPost() throws Exception {
        // Chiamata al metodo doPost ereditato da HttpServlet
        servlet.callDoPost(request, response);
        verify(response, never()).getWriter();

    }
}
