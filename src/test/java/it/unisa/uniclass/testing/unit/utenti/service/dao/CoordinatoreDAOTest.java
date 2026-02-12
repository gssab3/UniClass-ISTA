package it.unisa.uniclass.testing.unit.utenti.service.dao;

import it.unisa.uniclass.utenti.service.dao.CoordinatoreDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;

import static org.mockito.Mockito.*;

class CoordinatoreDAOTest {

    private EntityManager em;
    private TypedQuery<Coordinatore> coordinatoreQuery;
    private CoordinatoreDAO dao;

    @BeforeEach
    void setUp() {
        em = mock(EntityManager.class);
        coordinatoreQuery = mock(TypedQuery.class);

        dao = new CoordinatoreDAO();

        // Iniettiamo il mock dell'EntityManager via reflection
        try {
            var field = CoordinatoreDAO.class.getDeclaredField("emUniClass");
            field.setAccessible(true);
            field.set(dao, em);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    void testTrovaCoordinatoreEmailUniclass() {
        Coordinatore c = new Coordinatore();
        when(em.createNamedQuery(Coordinatore.TROVA_EMAIL, Coordinatore.class)).thenReturn(coordinatoreQuery);
        when(coordinatoreQuery.setParameter("email", "x@y.com")).thenReturn(coordinatoreQuery);
        when(coordinatoreQuery.getSingleResult()).thenReturn(c);

        assertEquals(c, dao.trovaCoordinatoreEmailUniclass("x@y.com"));
    }

    @Test
    void testTrovaCoordinatoreUniClass() {
        Coordinatore c = new Coordinatore();
        when(em.createQuery(Coordinatore.TROVA_COORDINATORE, Coordinatore.class)).thenReturn(coordinatoreQuery);
        when(coordinatoreQuery.setParameter("matricola", "123")).thenReturn(coordinatoreQuery);
        when(coordinatoreQuery.getSingleResult()).thenReturn(c);

        assertEquals(c, dao.trovaCoordinatoreUniClass("123"));
    }

    @Test
    void testTrovaCoordinatoriCorsoLaurea() {
        List<Coordinatore> list = Collections.singletonList(new Coordinatore());
        when(em.createQuery(Coordinatore.TROVA_COORDINATORE_CORSOLAUREA, Coordinatore.class)).thenReturn(coordinatoreQuery);
        when(coordinatoreQuery.setParameter("nomeCorsoLaurea", "Ingegneria")).thenReturn(coordinatoreQuery);
        when(coordinatoreQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaCoordinatoriCorsoLaurea("Ingegneria"));
    }

    @Test
    void testTrovaTutti() {
        List<Coordinatore> list = Collections.singletonList(new Coordinatore());
        when(em.createNamedQuery(Coordinatore.TROVA_TUTTI, Coordinatore.class)).thenReturn(coordinatoreQuery);
        when(coordinatoreQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaTutti());
    }

    @Test
    void testAggiungiCoordinatore() {
        Coordinatore c = new Coordinatore();
        dao.aggiungiCoordinatore(c);
        verify(em).merge(c);
    }

    @Test
    void testRimuoviCoordinatore() {
        Coordinatore c = new Coordinatore();
        dao.rimuoviCoordinatore(c);
        verify(em).remove(c);
    }
}
